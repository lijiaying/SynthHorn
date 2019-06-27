#*************************************************************************#
#*									 *#
#*		Makefile for the C5.0 system				 *#
#*		----------------------------				 *#
#*									 *#
#*************************************************************************#
.PHONY: clean

CC	= gcc -ffloat-store
LFLAGS = $(S) -static-libstdc++

src =\
	global.c\
	c50.c\
	construct.c\
	formtree.c\
	sort.c\
	info.c\
	discr.c\
	contin.c\
	subset.c\
	prune.c\
	p-thresh.c\
	trees.c\
	siftrules.c\
	ruletree.c\
	rules.c\
	getdata.c\
	implicitatt.c\
	mcost.c\
	confmat.c\
	update.c\
	attwinnow.c\
	classify.c\
	formrules.c\
	getnames.c\
	modelfiles.c\
	utility.c\
	xval.c\
	debug.c

cpp_src = $(wildcard *.cpp)
cpp_obj = $(subst .cpp,.o, $(cpp_src))


all: $(src) defns.i text.i Makefile $(cpp_obj) array.o
	cat defns.i $(src) | egrep -v 'defns.i|extern.i' >c50gt.c
	$(CC) $(LFLAGS) -D USEDOUBLE -D USE_ENDPOINT -O3 -o c5.0 c50gt.c $(cpp_obj) array.o -lm -lstdc++

$(cpp_obj): %.o: %.cpp
	$(CXX) -O3 -c $< -o $@

array.o: array.c array.h
	$(CC) $(CFLAGS) -c array.c
