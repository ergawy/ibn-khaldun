#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#define MAX_SUCCESSORS    10
#define MAX_PREDECESSORS  10
#define MAX_DOMINATORS    10
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
    CFGNode srcBB = cfgNodePool[srcBBOffset];

    while ((tok = strtok(NULL, " \n\t,")) != NULL) {
      /* log("[tok: %s] ", tok); */
      BBID destBBID = strtol(tok, NULL, 10);
      PoolOffset destBBOffset = getCFGNodeForBB(destBBID);
      CFGNode destBB = cfgNodePool[destBBOffset];

      srcBB.succs[srcBB.numSuccs] = destBBOffset;
      srcBB.numSuccs++;

      destBB.preds[destBB.numPreds] = srcBBOffset;
      destBB.numPreds++;
      /* log("%d, ", id); */
    }

    /* log("\n"); */
  }
}

/// Calculate dominance information as described in Section 9.2.1 of
/// "Engineering a compiler", 2011
static void calculateDominance() {

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
