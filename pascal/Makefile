# $Id: Makefile.to_nasm 556 2020-09-17 09:24:40Z coelho $
# compilation d'un compilateur

# export CLASSPATH=/usr/share/java/cup.jar:.

# executables
JAVAC	= javac -Xlint:unchecked
JAVA	= java
#JFLAGS	= -cp /usr/share/java/cup.jar:.
JFLAGS	= -cp /usr/share/java/java-cup-11b.jar:.

JLEX	= jflex
#JCUP	= cup
JCUP	= $(JAVA) $(JFLAGS) java_cup.Main

# compilation & execution chain
PASCAL  = java $(JFLAGS) Parser
ASM     = ./asm.py
RUN     = ./mach.py
TO_NASM = ./to_nasm.py

NASM    = nasm
NASM_FLAGS = -felf64

GCC     = gcc
GCC_ARG = -fno-pie -no-pie

# source files
F.jlex	= $(wildcard *.jlex)
F.cup	= $(wildcard *.cup)
F.p		= $(wildcard *.p)

default: help

help:
	@echo "help: this small help"
	@echo "clean: clean generated files"
	@echo "compile: compile the compiler"

clean:
	$(RM) *~ *.class *.java *.i *.o .compile *.obj *.asm $(F.p:%.p=%)

compile: .compile
.compile: $(F.cup) $(F.jlex)
	$(JCUP) -parser Parser $(F.cup)
	$(JLEX) $(F.jlex)
	$(JAVAC) $(JFLAGS) *.java
	touch $@

# disable all default rules
.SUFFIXES:

# pascal compilation
%.i: %.p; $(PASCAL) < $< > $@
# show generated code
%.y: %.i; cat $<
# assembler
%.o: %.i; $(ASM) < $< > $@
# eXecution
%.x: %.o; $(RUN) $<
# generate x86 asm
%.asm: %.i; $(TO_NASM) < $< > $@
# assemble x86 asm
%.obj: %.asm; $(NASM) $(NASM_FLAGS) -o $@ $<
# link executable
% : %.obj; $(GCC) $(GCC_ARG) $< -o $@

F.p	= $(wildcard *.p)
F.i	= $(F.p:%.p=%.i)
$(F.i): .compile
F.o	= $(F.i:%.i=%.o)
$(F.o): $(ASM)
F.x	= $(F.o:%.o=%.x)
$(F.x): $(RUN)

# distribution tar
.PHONY: tgz zip
tgz:
	tar -chvzf pascal.tgz Makefile *.py pascal.* test_00.p README

zip:
	zip compile.zip Makefile *.py pascal.* test_00.p README
