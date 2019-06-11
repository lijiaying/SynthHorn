#ifndef __COLOR_HH__
#define __COLOR_HH__

#include "llvm/Support/raw_ostream.h"
// #include <iostream>
// #include <string>
// #include <stdlib.h>
// #include <stdio.h>

#ifdef red
#undef red
#endif
#ifdef green
#undef green 
#endif
#ifdef yellow 
#undef yellow
#endif
#ifdef blue 
#undef blue 
#endif
#ifdef mag 
#undef mag 
#endif
#ifdef cyan
#undef cyan 
#endif
#ifdef gray
#undef gray
#endif
#ifdef normal
#undef normal
#endif
#ifdef bold
#undef bold
#endif
#ifdef underline 
#undef underline 
#endif

#define red "\e[31m"
#define green "\e[32m"
#define yellow "\e[33m"
#define blue "\e[34m"
#define mag "\e[35m"
#define cyan "\e[36m"
#define gray "\e[37m"

#define normal "\e[0m"
#define bold "\e[1m"
#define underline "\e[4m"


#ifdef LOG
#undef LOG
#endif
#ifdef LOGIT
#undef LOGIT
#endif
#ifdef LOGDP
#undef LOGDP
#endif
#ifdef LOGLINE
#undef LOGLINE
#endif

static std::string function = " ====[ Start tracing ]=== ";
static std::string line;
// char cur_line[10]; \
// sprintf(cur_line, "%d", __LINE__); \

#define _NULL_LOG(TAG, CODE) do {} while(0)
#define _PURE_LOG(TAG, CODE) do {CODE;} while(0)
#define _LOCT_LOG(TAG, CODE) do { \
	if (__FUNCTION__ != function) { \
		llvm::errs() << blue << "<<< ****** function: " << function << " ****** <<<\n\n" << normal; \
		function = __FUNCTION__;\
		llvm::errs() << green << ">>> ****** function: " << function << " ****** >>>\n" << normal; \
	} \
	llvm::errs() << red << "#" << __LINE__ << normal << ": "; \
	CODE; \
	llvm::errs().flush();\
} while (0);


#define LOG(TAG, CODE) _NULL_LOG(TAG, CODE)
#define LOGIT(TAG, CODE) _PURE_LOG(TAG, CODE)
#define LOGDP(TAG, CODE) _LOCT_LOG(TAG, CODE)
#define LOGLINE(TAG, CODE) _LOCT_LOG(TAG, CODE)

#endif
