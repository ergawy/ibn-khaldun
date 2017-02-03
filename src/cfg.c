#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#define MAX_SUCCESSORS    10
#define MAX_PREDECESSORS  10
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

typedef struct CFGNode {
  int id;
  // An array of pointer offsets into the global memory block allocated for
  // all CFG nodes. The reason for storing indices rather than actual pointers
  // is that I don't know the max expected number of BB in the input program
  // and thus I use realloc which might move the originally allocated block
  // to a different place in memory invalidating old pointers.
  int succs[MAX_SUCCESSORS];
  int numSuccs;

  int preds[MAX_PREDECESSORS];
  int numPreds;
} CFGNode, *CFGNodePtr;

// The entry BB is stored as the first object of the pool.
static CFGNodePtr cfgNodePool = NULL;
static int currentPoolSize = 0;
static int currentNumCFGNodes = 0;
static char cfgSpecLine[MAX_SPEC_LINE_LEN];

static CFGNodePtr getCFGNodeForBB(int bbID);
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
    int srcID = strtol(tok, NULL, 10);
    /* log("%d: ", id); */
    CFGNodePtr srcBB = getCFGNodeForBB(srcID);

    while ((tok = strtok(NULL, " \n\t,")) != NULL) {
      /* log("[tok: %s] ", tok); */
      int destID = strtol(tok, NULL, 10);
      CFGNodePtr destBB = getCFGNodeForBB(destID);
      srcBB->succs[srcBB->numSuccs] = destID;
      srcBB->numSuccs++;

      destBB->preds[destBB->numPreds] = srcID;
      destBB->numPreds++;
      /* log("%d, ", id); */
    }

    /* log("\n"); */
  }
}

static CFGNodePtr getCFGNodeForBB(int bbID) {
  for (int i=0 ; i<currentNumCFGNodes ; i++) {
    if (cfgNodePool[i].id == bbID) {
      /* log("Found node for %d\n", bbID); */
      return (cfgNodePool + i);
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
  return cfgNodePool + currentNumCFGNodes - 1;
}

static void release_memory(CFGNodePtr bb) {
  if (bb != NULL) {
    for (int i=0 ; i<bb->numSuccs ; i++) {
      release_memory(cfgNodePool + bb->succs[i]);
    }
  }
}
