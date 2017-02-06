#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#define MAX_SUCCESSORS    16
#define MAX_PREDECESSORS  16
#define MAX_DOMINATORS    128
#define MAX_SPEC_LINE_LEN 128

#define log(msg, ...)                           \
  fprintf(stdout, (msg), ## __VA_ARGS__)

// Avoid doule evaluation by using GCC's __auto_type feature
// https://gcc.gnu.org/onlinedocs/gcc-4.9.2/gcc/Typeof.html#Typeof
// This equivalent to using C++11's auto keyword
#define max(a,b)           \
  ({ __auto_type _a = (a); \
     __auto_type _b = (b); \
     _a > _b ? _a : _b; })

typedef int BBID;
typedef int PoolOffset;
typedef int bool;

#define TRUE  1
#define FALSE 0

typedef struct CFGNode {
  BBID id;
  // An array of pointer offsets into the global memory block allocated for
  // all CFG nodes. The reason for storing indices rather than actual pointers
  // is that I don't know the max expected number of BB in the input program
  // and thus I use realloc which might move the originally allocated block
  // to a different place in memory invalidating old pointers.
  PoolOffset succs[MAX_SUCCESSORS];
  int numSuccs;

  PoolOffset preds[MAX_PREDECESSORS];
  int numPreds;

  // dominators of the BB
  PoolOffset doms[MAX_DOMINATORS];
  int numDoms;
} CFGNode, *CFGNodePtr;

// The entry BB is stored as the first object of the pool.
static CFGNodePtr cfgNodePool = NULL;
static int currentPoolSize = 0;
static int currentNumCFGNodes = 0;
static char cfgSpecLine[MAX_SPEC_LINE_LEN];

static PoolOffset get_cfg_node_for_bb(BBID bbID);
static void release_memory(CFGNodePtr bb);
static void calculate_dominance();
static void calculate_reverse_post_order(PoolOffset bbOffset, int *pot,
                                      int *rpot, bool *visited);
static bool update_dom_set(PoolOffset bbOffset);
static void intersect_dom_sets(PoolOffset *dest, int *destSize,
                             PoolOffset *src, int *srcSize);
static void print_cfg_node(PoolOffset bbOffset);

void parse_cgf_from_file(FILE *in) {
  if (cfgNodePool != NULL) {
    release_memory(cfgNodePool);
    free(cfgNodePool);
  }

  while (fgets(cfgSpecLine, MAX_SPEC_LINE_LEN, in) != NULL) {
    char *tok = strtok(cfgSpecLine, " \n\t:");

    if (tok == NULL || *tok == '!') {
      continue;
    }

    BBID srcBBID = strtol(tok, NULL, 10);
    PoolOffset srcBBOffset = get_cfg_node_for_bb(srcBBID);
    CFGNodePtr srcBB = cfgNodePool + srcBBOffset;

    while ((tok = strtok(NULL, " \n\t,")) != NULL) {
      BBID destBBID = strtol(tok, NULL, 10);
      PoolOffset destBBOffset = get_cfg_node_for_bb(destBBID);
      CFGNodePtr destBB = cfgNodePool + destBBOffset;

      srcBB->succs[srcBB->numSuccs] = destBBOffset;
      srcBB->numSuccs++;

      destBB->preds[destBB->numPreds] = srcBBOffset;
      destBB->numPreds++;
    }
  }

  calculate_dominance();
}

/// Calculate dominance information as described in Section 9.2.1 of
/// "Engineering a compiler", 2011
static void calculate_dominance() {
  // The entry node only dominates itself
  cfgNodePool[0].doms[0] = 0;
  cfgNodePool[0].numDoms = 1;

  for (int i=1 ; i<currentNumCFGNodes ; i++) {
    // If the number of dominators of a BB is 0, then this BB is dominated
    // by all other BBs. In other words, the number of dominators is
    // actually currentNumCFGNodes.
    //
    // I did that since I use fixed sized arrays with max sizes. The
    // dominators set of and BB starts huge (includes all the BBs in the
    // CFG) during the initialization step and then shrinks. Instead of
    // unnecessarily creating huge sets of dominators an empty dominator
    // set signals an includes-all set
    //
    // This is fine since any BB at least dominates itself.
    cfgNodePool[i].numDoms = 0;
  }

  int *rpot = malloc(currentNumCFGNodes * sizeof(int));
  bool *visited = calloc(currentNumCFGNodes, sizeof(bool));
  int pot = 0;
  calculate_reverse_post_order(0, &pot, rpot, visited);

  bool changed = TRUE;

  while(changed) {
    changed = FALSE;

    // Update the dom sets of BB's according to their reverse-post-order
    // traversal.
    for (int i=1 ; i<currentNumCFGNodes ; i++) {
      changed |= update_dom_set(rpot[i]);
      print_cfg_node(rpot[i]);
    }
  }

  free(rpot);
  free(visited);
}

/// Updates the dominator set of the BB stored at bbOffset by taking the
/// intersection of all dom sets of predecessors and adding the BB to the
/// result if not already there.
///
/// Returns true if the dom set was changed and false otherwise.
///
/// FIXME: for now a very inefficient representation of sets and a poor
/// implementation of union-find is provided. Implement a better solution
/// by following e.g. Chapter 21 in CLRS. Probably start a repo for
/// something like the STL.
static bool update_dom_set(PoolOffset bbOffset) {
  CFGNodePtr n = cfgNodePool + bbOffset;
  int oldNumDoms = n->numDoms;
  PoolOffset tempSet[MAX_DOMINATORS];
  int tempSetSize = 0;
  
  for (int i=0 ; i<n->numPreds ; i++) {
    CFGNodePtr pred = cfgNodePool + n->preds[i];
    intersect_dom_sets(tempSet, &tempSetSize, pred->doms,
                     &(pred->numDoms));
  }

  bool found = FALSE;
  for (int i=0 ; i<tempSetSize ; i++) {
    if (tempSet[i] == bbOffset) {
      found = TRUE;
      break;
    }
  }

  if (!found) {
    tempSet[tempSetSize] = bbOffset;
    tempSetSize++;
  }

  memcpy(n->doms, tempSet, tempSetSize * sizeof(PoolOffset));
  n->numDoms = tempSetSize;
  return oldNumDoms != tempSetSize;
}

static void intersect_dom_sets(PoolOffset *dest, int *destSize,
                             PoolOffset *src, int *srcSize) {
  log("##################\n");
  log("Intersecting 2 sets:\n");
  log("\tfirst set: [");
  if (*destSize == 0) {
    log("FULL SET");
  } else {
    for (int i=0 ; i<*destSize ; i++) {
      log("%d", cfgNodePool[dest[i]].id);
      log(i<(*destSize)-1 ? ", " : "");
    }
  }
  log("]\n");
  log("\tsecond set: [");
  if (*srcSize == 0) {
    log("FULL SET");
  } else {
    for (int i=0 ; i<*srcSize ; i++) {
      log("%d", cfgNodePool[src[i]].id);
      log(i<(*srcSize)-1 ? ", " : "");
    }
  }
  log("]\n");

  // if dest is the full set, then just copy the src set
  if (*destSize == 0) {
    *destSize = *srcSize;
    memcpy(dest, src, *srcSize * sizeof(PoolOffset));
    // NOTE we don't need to check if src is full since we are calculating
    // dest = intersect(dest, src)
  } else if (*srcSize > 0) {
    PoolOffset res[MAX_DOMINATORS];
    int resSize = 0;

    for (int i=0 ; i<*destSize ; i++) {
      for (int j=0 ; j<*srcSize ; j++) {
        if (dest[i] == src[j]) {
          res[resSize++] = dest[i];
        }
      }
    }

    *destSize = resSize;
    memcpy(dest, res, resSize * sizeof(PoolOffset)); 
  }

  log("\tresult: [");
  if (*destSize == 0) {
    log("FULL SET");
  } else {
    for (int i=0 ; i<*destSize ; i++) {
      log("%d", cfgNodePool[dest[i]].id);
      log(i<(*destSize)-1 ? ", " : "");
    }
  }
  log("]\n");
  log("$$$$$$$$$$$$$$$$$$\n");
}

// pot is the post-order traversal index of the current node
// rpot is a int -> PoolOffset map that specifies the reverse post order
// traversal of the CFG
static void calculate_reverse_post_order(PoolOffset bbOffset, int *pot,
                                      int *rpot, bool *visited) {
  assert(bbOffset < currentNumCFGNodes && "Invalid BB");

  if (visited[bbOffset]) {
    return;
  }

  CFGNodePtr bb = cfgNodePool + bbOffset;
  visited[bbOffset] = TRUE;
  for (int i=0 ; i<bb->numSuccs ; i++) {
    calculate_reverse_post_order(bb->succs[i], pot, rpot, visited);
  }

  rpot[currentNumCFGNodes-1-*pot] = bbOffset;
  ++*pot;
}

/// Search for the CFGNode correspomding to the passed bbID and if found
/// return it. Otherwise, take a new node from the pool and assign it to
/// the BB.
static PoolOffset get_cfg_node_for_bb(BBID bbID) {
  for (int i=0 ; i<currentNumCFGNodes ; i++) {
    if (cfgNodePool[i].id == bbID) {
      return i;
    }
  }

  // The pool is full, double its size.
  if (currentNumCFGNodes == currentPoolSize) {
    currentPoolSize = max(1, currentPoolSize*2);
    cfgNodePool = realloc(cfgNodePool,
                          currentPoolSize*sizeof(CFGNode));
    assert(cfgNodePool != NULL && "Ran out of virtual memory\n");
  }

  assert(currentNumCFGNodes < currentPoolSize
         && "Exceeded pool allocated size\n");
  cfgNodePool[currentNumCFGNodes].id = bbID;
  cfgNodePool[currentNumCFGNodes].numSuccs = 0;
  cfgNodePool[currentNumCFGNodes].numPreds = 0;
  currentNumCFGNodes++;
  return currentNumCFGNodes - 1;
}

static void release_memory(CFGNodePtr bb) {
  if (bb != NULL) {
    for (int i=0 ; i<bb->numSuccs ; i++) {
      release_memory(cfgNodePool + bb->succs[i]);
    }
  }
}

static void print_cfg_node(PoolOffset bbOffset) {
  CFGNodePtr n = cfgNodePool + bbOffset;
  log("==================\n");
  log("BBID: %d\n", n->id);

  log("# Preds: %d [", n->numPreds);
  for (int i=0 ; i<n->numPreds ; i++) {
    log("%d", cfgNodePool[n->preds[i]].id);
    log(i<(n->numPreds-1) ? ", " : "");
  }
  log("]\n");

  log("# Succs: %d [", n->numSuccs);
  for (int i=0 ; i<n->numSuccs ; i++) {
    log("%d", cfgNodePool[n->succs[i]].id);
    log(i<(n->numSuccs-1) ? ", " : "");
  }
  log("]\n");

  log("# Doms: %d [", n->numDoms);
  for (int i=0 ; i<n->numDoms ; i++) {
    log("%d", cfgNodePool[n->doms[i]].id);
    log(i<(n->numDoms-1) ? ", " : "");
  }
  log("]\n");

  log("------------------\n");
}
