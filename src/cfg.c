#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>

#define MAX_SUCCESSORS    10
#define MAX_SPEC_LINE_LEN 128

#define log(msg, ...)                           \
  fprintf(stdout, (msg), ## __VA_ARGS__)

typedef struct CFGNode {
  int id;
  // An array of pointer offsets into the global memory block allocated for
  // all CFG nodes. The reason for storing indices rather than actual pointers
  // is that I don't know the max expected number of BB in the input program
  // and thus I use realloc which might move the originally allocated block
  // to a different place in memory invalidating old pointers.
  int succs[MAX_SUCCESSORS];
  int numSuccs;
} CFGNode, *CFGNodePtr;

// The entry BB is stored as the first object of the pool.
static CFGNodePtr cfgNodePool = NULL;
static char cfgSpecLine[MAX_SPEC_LINE_LEN];

static void release_memory(CFGNodePtr bb);

void parse_cgf_from_file(FILE *in) {
  if (cfgNodePool != NULL) {
    release_memory(cfgNodePool);
    free(cfgNodePool);
  }

  // Allocate an initially small pool
  int currentPoolSize = 16;
  cfgNodePool = (CFGNodePtr)malloc(currentPoolSize * sizeof(CFGNode));
  int currentBB = 0;
  int parsedBB = 0;

  while (fgets(cfgSpecLine, MAX_SPEC_LINE_LEN, in) != NULL) {
    char *tok = strtok(cfgSpecLine, " \n\t:");

    if (tok == NULL || *tok == '!') {
      continue;
    }

    /* log("[tok: %s] ", tok); */
    int id = strtol(tok, NULL, 10);
    log("%d: ", id);

    while ((tok = strtok(NULL, " \n\t,")) != NULL) {
      /* log("[tok: %s] ", tok); */
      id = strtol(tok, NULL, 10);
      log("%d, ", id);
    }

    log("\n");
  }
}

static void release_memory(CFGNodePtr bb) {
  if (bb != NULL) {
    for (int i=0 ; i<bb->numSuccs ; i++) {
      release_memory(cfgNodePool + bb->succs[i]);
    }
  }
}
