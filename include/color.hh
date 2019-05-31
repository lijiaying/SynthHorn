#ifndef __COLOR_HH__
#define __COLOR_HH__

#include "llvm/Support/raw_ostream.h"
// #include <iostream>
// #include <string>
// #include <stdlib.h>
// #include <stdio.h>

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

static std::string function = "Start tracing ---";
static std::string line;

// #define LOG(TAG, CODE) do {} while(0)

#define LOG(TAG, CODE) do { \
	if (__FUNCTION__ != function) { \
		llvm::errs() << blue << "<<< ****** function: " << function << " ****** <<<\n\n" << normal; \
		function = __FUNCTION__;\
		llvm::errs() << green << ">>> ****** function: " << function << " ****** >>>\n" << normal; \
	} \
	char cur_line[10]; \
	sprintf(cur_line, "%d", __LINE__); \
	if (cur_line != line) { \
		line = cur_line; \
		llvm::errs() << red << "#" << line << normal << ": "; \
		CODE; \
		llvm::errs().flush();\
	} \
} while (0);


#endif