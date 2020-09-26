#!/usr/bin/env python3

import sys, re
# error messages and counting
errors = 0

def err(msg):
    print('## ot_nasm.py Error: ' + msg, file=sys.stderr)
    global errors
    errors += 1

def encode_label(label):
    return ".usr_"+label

# read all input
lines = sys.stdin.readlines()

# define re for names
IDENT = '[_@%a-zA-Z][_@%a-zA-Z0-9:]*'
something = re.compile(r'.*\w')
comment_re = re.compile(r'\s*;/')
label_re = re.compile('^' + IDENT + '\s+EQU')
var_re = re.compile('^' + IDENT + '\s+DS\s+\d+')

# define re for commands
command = re.compile(
    r'BGZ|BEZ|PUSH|LOAD|STORE|SWAP|ADD|SUB|MUL|DIV|AND|OR|NOT|STOP|GOTO|IN|OUT'
)
push = re.compile(r'\s+PUSH\s+' + IDENT + '\s*')
pushInt = re.compile(r'\s+PUSH\s+\d*\s*')
bez = re.compile(r'\s+BEZ\s+' + IDENT + '\s*')
bgz = re.compile(r'\s+BGZ\s+' + IDENT + '\s*')
load = re.compile(r'\s+LOAD\s*')
store = re.compile(r'\s+STORE\s*')
swap = re.compile(r'\s+SWAP\s*')
add = re.compile(r'\s+ADD\s*')
sub = re.compile(r'\s+SUB\s*')
mul = re.compile(r'\s+MUL\s*')
div = re.compile(r'\s+DIV\s*')
And = re.compile(r'\s+AND\s*')
Or = re.compile(r'\s+OR\s*')
Not = re.compile(r'\s+NOT\s*')
stop = re.compile(r'\s+STOP\s*')
goto = re.compile(r'\s+GOTO\s*')
In = re.compile(r'\s+IN\s*')
Out = re.compile(r'\s+OUT\s*')


commandArg = re.compile(r'BGZ|BEZ|PUSH')


# asm included in the result
header = """
global main
extern printf
extern scanf
section .text
main:
    push rbp
    mov rbp, rsp
    mov r13, rsp
.body:
"""

footer = """
.end: 
    mov rsp, r13
    pop rbp
    ret
print:
    mov rdi, out_msg
    mov rsi, [rsp + 8]
    xor rax, rax
    mov r12, rsp
    and rsp, 0xfffffffffffffff0
    call printf WRT ..plt
    mov rsp, r12
    ret
input:
    mov rdi, in_msg
    xor rax, rax
    mov r12, rsp
    and rsp, 0xfffffffffffffff0
    call printf WRT ..plt
    mov rsp, r12

    mov rdi, in_format
    lea rsi, [rsp + 8]
    xor rax, rax
    mov r12, rsp
    and rsp, 0xfffffffffffffff0
    call scanf WRT ..plt
    mov rsp, r12
    ret
out_msg:    db `out> %ld\\n`,0
in_msg:     db "in> ",0
in_format:  db "%ld",0
section .bss
data: resq 1000000
"""

# constant or identifier
Arg = re.compile('^(\d+|' + IDENT + ')$')

# already defined names
dico = {}
# current line and memory extension...
line = 0
mem = 0

ln = 0
for l in lines:
    ln += 1
    if something.match(l) and not comment_re.match(l):
        l = l.split(';/')[0]  # drop inline comments
        tokens = l.split(None)
        if label_re.match(l):
            label = tokens[0]
            if label in dico:
                err('Duplicate key label %s at line %d' % (label, ln))
            else:
                dico[label] = encode_label(label)
        elif var_re.match(l):  # XXX DS 123
            var, size = tokens[0], tokens[2]
            if var in dico:
                err('Duplicate key var %s at line %d' % (var, ln))
            else:
                dico[var] = mem
                mem += int(size)
        elif command.match(tokens[0]):
            cmd = tokens[0]
            if commandArg.match(cmd):
                if len(tokens) < 2:
                    err('Missing %s argument at line %d' % (cmd, ln))
                elif not Arg.match(tokens[1]):
                    err('Bad argument for %s at line %d: %s' % (cmd, ln,
                                                                tokens[1]))
            elif len(tokens) > 1:
                err('Command %s does not except arguments (%s) at line %d' %
                    (cmd, tokens[1], ln))
            line += len(l.split(None))
        else:
            err('Unknown command "%s" at line %d' % (tokens[0], ln))

output = ""

ln = 0
for l in lines:
    ln += 1
    l = l.split(';/')[0].strip('\n')
    tokens = l.split(None)
    if push.match(l):
        try:
            output += '\npush %s' % dico[tokens[1]] + '\n'
        except KeyError:
            err('Undefined key %s at line %d' % (tokens[1], ln))
    elif pushInt.match(l):
        output += 'push %s' % tokens[1] + '\n'
    elif bez.match(l):
        try:
            output += '\npop rax\n'
            output += 'test rax, rax\n'
            output += 'jz %s' % dico[tokens[1]] + '\n'
        except KeyError:
            err('Undefined key %s at line %d' % (tokens[1], ln))
    elif bgz.match(l):
        try:
            output += '\npop rax\n'
            output += 'cmp rax, 0\n'
            output += 'jg %s' % dico[tokens[1]] + '\n'
        except KeyError:
            err('Undefined key %s at line %d' % (tokens[1], ln))
    elif load.match(l):
        output += """
pop rdi
mov rax, [ rdi * 8 + data]
push rax
"""
    elif store.match(l):
        output += """
pop rax
pop rdi
mov [rdi * 8 + data], rax
"""
    elif add.match(l):
        output += """
pop rax
add [rsp], rax
"""
    elif sub.match(l):
            output += """
pop rax
sub [rsp], rax
"""
    elif div.match(l):
            output += """
pop rdi
pop rax
mov rdx, 0
div rdi
push rax
"""

    elif mul.match(l):
            output += """
pop rax
mul qword [rsp]
mov [rsp], rax
"""

    elif swap.match(l):
            output += """
pop rax
pop rdi
push rax
push rdi
"""

    elif And.match(l):
            output += """
pop rax
and [rsp], rax
"""

    elif Not.match(l):
            output += """
pop rax
not rax
push rax
"""
    elif Or.match(l):
                output += """
pop rax
or [rsp], rax
"""
    elif goto.match(l):
            output += """
pop rax
jmp rax
"""
    elif In.match(l):
                output += """
push 0
call input
"""
    elif Out.match(l):
                output += """
call print
"""
    elif stop.match(l):
                output += """
jmp .end
"""
    elif label_re.match(l):
        label = tokens[0]
        if label in dico:
            output += "%s:\n" % dico[label]
        else:
            err('Label not found: %s at line %d' % (label, ln))
    elif (something.match(l)
          and not (var_re.match(l)
                   or comment_re.match(l))):
        err("Unexpexted line: %s" % l)

if errors:  # show final error count
    err('%d errors' % errors)
    sys.exit(1)
else:
    print(header)
    print(output)
    print(footer)

