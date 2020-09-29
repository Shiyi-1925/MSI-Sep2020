











	PUSH	findec_0
	GOTO
@foo	EQU	*
;/ print...
	PUSH	3
	OUT
	GOTO
findec_0	EQU	*
	PUSH	ret_1
	PUSH	@foo
	GOTO
ret_1	EQU	*
	STOP

