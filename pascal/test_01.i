
































a	DS	1
	PUSH	a
	PUSH	24
	STORE
b	DS	1
	PUSH	b
	PUSH	18
	STORE
c	DS	1
entree_0	EQU	*
	PUSH	b
	LOAD
	BEZ	sortie_0
	PUSH	c
	PUSH	a
	LOAD
	PUSH	b
	LOAD
	PUSH	a
	LOAD
	PUSH	b
	LOAD
	DIV
	MUL
	SUB
	STORE
	PUSH	a
	PUSH	b
	LOAD
	STORE
	PUSH	b
	PUSH	c
	LOAD
	STORE
	PUSH	entree_0
	GOTO
sortie_0	EQU	*
;/ print...
	PUSH	a
	LOAD
	OUT
;/ print...
	PUSH	b
	LOAD
	OUT
	STOP

