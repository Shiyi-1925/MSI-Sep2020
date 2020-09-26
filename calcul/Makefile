# $Id: Makefile 552 2020-09-17 09:12:44Z coelho $

JAVAC	= javac -Xlint:unchecked
JAVA	= java
JFLAGS	= -cp /usr/share/java/java-cup-11b.jar:.

LEX	= jflex
#YACC	= cup
YACC	= $(JAVA) $(JFLAGS) java_cup.Main

all: clean

compile:
	$(LEX) calcul.jlex
	$(YACC) -parser Parser calcul.cup
	$(JAVAC) $(JFLAGS) *.java

run: compile
	$(JAVA) $(JFLAGS) Parser

clean:
	$(RM) Lexer.java Parser.java sym.java *~ *.class
