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
  ({ __auto_type _a = (a);        \
     __auto_type _b = (b);        \
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

static PoolOffset getCFGNodeForBB(BBID bbID);
static void release_memory(CFGNodePtr bb);
static void calculateDominance();
static void calculateReversePostOrder(PoolOffset bbOffset, int *pot,
                                      int *rpot, bool *visited);

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

    /* log("[tok: %s] ", tok); */
    BBID srcBBID = strtol(tok, NULL, 10);
    /* log("%d: ", id); */
    PoolOffset srcBBOffset = getCFGNodeForBB(srcBBID);
    CFGNodePtr srcBB = cfgNodePool + srcBBOffset;

    while ((tok = strtok(NULL, " \n\t,")) != NULL) {
      /* log("[tok: %s] ", tok); */
      BBID destBBID = strtol(tok, NULL, 10);
      PoolOffset destBBOffset = getCFGNodeForBB(destBBID);
      CFGNodePtr destBB = cfgNodePool + destBBOffset;

      srcBB->succs[srcBB->numSuccs] = destBBOffset;
      srcBB->numSuccs++;

      destBB->preds[destBB->numPreds] = srcBBOffset;
      destBB->numPreds++;
      /* log("%d, ", id); */
    }

    /* log("\n"); */
  }

  calculateDominance();
}

/// Calculate dominance information as described in Section 9.2.1 of
/// "Engineering a compiler", 2011
///
/// FIXME: for now a very inefficient representation of sets a poor
/// implementation of union-find is provided. Implement a better solution
/// by following e.g. Chapter 21 in CLRS. Probably start a repo for
/// something like the STL.
static void calculateDominance() {
  cfgNodePool[0].doms[0] = 0;
  cfgNodePool[0].numDoms = 1;

  for (int i=1 ; i<currentNumCFGNodes ; i++) {
    // If the number of dominators of a BB is 0, then this BB is dominated
    // by all other BBs. In other words, the number of dominators is
    // actually currentNumCFGNodes.
    //
    // I did since I use fixed sized arrays with max sizes. The dominators
    // set of and BB starts huge (includes all the BBs in the CFG) during
    // the initialization step and then shrinks. Instead of unnecessarily
    // creating huge sets of dominators an empty dominator set signals an
    // including all set
    cfgNodePool[i].numDoms = 0;
  }

  int *rpot = malloc(currentNumCFGNodes*sizeof(int));
  bool *visited = malloc(currentNumCFGNodes*sizeof(bool));
  int pot = 0;
  calculateReversePostOrder(0, &pot, rpot, visited);

  for (PoolOffset i=0 ; i<currentNumCFGNodes ; i++) {
    log("%d -> %d\n", cfgNodePool[i].id, rpot[i]);
  }

  /* bool changed = TRUE; */

  /* while(changed) { */
  /*   changed = FALSE; */

  /*   for (int i=1 ; i<currentNumCFGNodes ; i++) { */
      
  /*   } */
  /* } */

  free(rpot);
  free(visited);
}

// pot is the post-order traversal index of the current node
// rpot is a PoolOffset -> int map that specifies the reverse post order
// traversal of the CFG
static void calculateReversePostOrder(PoolOffset bbOffset, int *pot,
                                      int *rpot, bool *visited) {
  assert(bbOffset < currentNumCFGNodes && "Invalid BB");

  if (visited[bbOffset]) {
    return;
  }

  CFGNodePtr bb = cfgNodePool + bbOffset;
  visited[bbOffset] = TRUE;
  /* log("%d: numSuccs(%d)\n", bbOffset, bb->numSuccs); */

  for (int i=0 ; i<bb->numSuccs ; i++) {
    log("from %d to %d\n", cfgNodePool[bbOffset].id,
        cfgNodePool[bb->succs[i]].id);
    calculateReversePostOrder(bb->succs[i], pot, rpot, visited);
  }

  rpot[bbOffset] = currentNumCFGNodes - 1 - *pot;
  log("%d -->> %d\n", bbOffset, *pot);
  ++*pot;
}

static int getCFGNodeForBB(BBID bbID) {
  for (int i=0 ; i<currentNumCFGNodes ; i++) {
    if (cfgNodePool[i].id == bbID) {
      /* log("Found node for %d\n", bbID); */
      return i;
    }
  }

  if (currentNumCFGNodes == currentPoolSize) {
    /* log("Increased pool size from %d to %d\n", currentPoolSize, */
    /*     max(1,currentPoolSize*2)); */
    currentPoolSize = max(1, currentPoolSize*2);
    cfgNodePool = realloc(cfgNodePool,
                          currentPoolSize*sizeof(CFGNode));
    assert(cfgNodePool != NULL && "Ran out of virtual memory\n");
  }

  assert(currentNumCFGNodes < currentPoolSize
         && "Exceeded pool allocated size\n");
  /* log("Created a new node for %d\n", bbID); */
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
