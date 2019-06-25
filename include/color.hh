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
#ifdef lred
#undef lred
#endif
#ifdef lgreen
#undef lgreen 
#endif
#ifdef lyellow 
#undef lyellow
#endif
#ifdef lblue 
#undef lblue 
#endif
#ifdef lmag 
#undef lmag 
#endif
#ifdef lcyan
#undef lcyan 
#endif
#ifdef lgray
#undef lgray
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

/*
static enum {normal=0, bold, underline=4, red=31, green, yellow, blue, mag, cyan, gray, light_gray=91, light_red, light_green, light_yellow, light_blue, light_mag, light_cyan} _color_;

inline std::string background(enum color c) {
	return "\e[37m;" + std::to_string(c+10) + "m";
}

inline std::string foreground(enum color c) {
	return "\e[" + std::to_string(c) + "m";
}
*/


#define red "\e[31;40m"
#define green "\e[32;40m"
#define yellow "\e[33;40m"
#define blue "\e[34;40m"
#define mag "\e[35;40m"
#define cyan "\e[36;40m"
#define lgray "\e[37;40m"
#define gray "\e[90;40m"
#define lred "\e[91;40m"
#define lgreen "\e[92;40m"
#define lyellow "\e[93;40m"
#define lblue "\e[94;40m" 
#define lmag "\e[95;40m"
#define lcyan "\e[96;40m"

#define bred "\e[37;41m"
#define bgreen "\e[37;42m"
#define byellow "\e[37;43m"
#define bblue "\e[37;44m"
#define bmag "\e[37;45m"
#define bcyan "\e[37;46m"
#define blgray "\e[37;47m"
#define bgray "\e[37;100m"
#define blred "\e[37;101m"
#define blgreen "\e[37;102m"
#define blyellow "\e[37;103m"
#define blblue "\e[37;104m" 
#define blmag "\e[37;105m"
#define blcyan "\e[37;106m"

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
#define _LINE_LOG(TAG, CODE) do { \
	std::string filestr = __FILE__;\
	int loc = filestr.rfind("/");\
	loc = filestr.rfind("/", loc-1);\
	loc = filestr.rfind("/", loc-1);\
	filestr = filestr.substr(loc+1);\
	llvm::errs() << gray << underline << "<" << filestr << ":L" << __LINE__ << ">" << normal << " "; \
	CODE; \
	llvm::errs().flush();\
} while (0)

#define _LOCT_LOG_OLD(TAG, CODE) do { \
	if (__FUNCTION__ != function) { \
		llvm::errs() << blue << "<<< ****** function: " << function << " ****** <<<\n\n" << normal; \
		function = __FUNCTION__;\
		llvm::errs() << green << ">>> ****** function: " << function << " ****** >>>\n" << normal; \
	} \
} while (0)

#define _LOCT_LOG(TAG, CODE) do { \
	std::string filestr = __FILE__;\
	int loc = filestr.rfind("/");\
	loc = filestr.rfind("/", loc-1);\
	loc = filestr.rfind("/", loc-1);\
	filestr = filestr.substr(loc+1);\
	llvm::errs() << gray << underline << "<" << filestr << ":L" << __LINE__ << ">" << normal << " "; \
	CODE; \
	llvm::errs().flush();\
} while (0)


#define LOG(TAG, CODE) _NULL_LOG(TAG, CODE)
#define LOGIT(TAG, CODE) _PURE_LOG(TAG, CODE)
#define LOGDP(TAG, CODE) _LOCT_LOG(TAG, CODE)
#define LOGLINE(TAG, CODE) _LINE_LOG(TAG, CODE)
#define LOGLOC(TAG, CODE) _LOCT_LOG(TAG, CODE)

#endif
