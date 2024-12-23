
---
weight: 2
title: "SVA Quick Reference"
description: "SystemVerilog Assertion Quick Reference；SVA Quick Reference"

---

**NOTE**: This SVA Quick Reference Manual currently supports the IEEE 1800-2005 standard.

## Binding

```systemverilog
bind target bind_obj [ (params)] bind_inst (ports) ;
```
Attaches a SystemVerilog module or interface to a Verilog module or interface instance, or to a VHDL entity/architecture. Multiple targets supported. Example:

```systemverilog
bind fifo fifo_full v1(clk,empty,full); 
bind top.dut.fifo1 fifo_full v2(clk,empty,full); 
bind fifo:fifo1,fifo2 fifo_full v3(clk,empty,full);
```

## Immediate Assertions

```systemverilog
[ label : ] assert (boolean_expr) [ action_block ] ;
```
Tests an expression when the statement is executed in the procedural code. Example:

```systemverilog
enable_set_during_read_op_only : assert (state >= `start_read && state <= `finish_read); 
else $warning("Enable set when state => %b", state);
```

## Declarations

### Sequence

```systemverilog
sequence identifier [ argument_list ] ;
sequence_expr [ seq_op sequence_expr ] ... ; 
endsequence [ : identifier ] 
```
Declares a sequence expression that can be used in property declarations. Local variables are permitted. Example:

```systemverilog
sequence BusReq (bit REQ=0, bit ACK=0); 
REQ ##[1:3] ACK; 
endsequence
```

### Property

```systemverilog
property identifier [ argument_list ] ;
[ clock_expr ] [ disable_clause ] property_expr ; 
endproperty [ : identifier ] 
```
Declares a condition or sequence to be verified during simulation. Local variables are permitted. Example:

```systemverilog
property P6 (bit AA, BB=`true, EN=1); 
@(negedge clk) EN -> (BB ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## Directives

### Assert Property

```systemverilog
[ label : ] assert property (prop_expr) [ action_block ] ;
```
Checks a property during verification. Example:

```systemverilog
property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty 
assert property (P5(a));
```

### Assume Property

```systemverilog
[label:] assume property (prop_expr) [ action_block ] ;
```
Constrains the inputs considered for the property during verification. In simulation, treated like assert. Example:

```systemverilog
A1: assume (@(ena) !rst);
```

### Cover Property

```systemverilog
[label:] cover property (prop_expr) [ pass_statement ] ; 
[label:] cover sequence (seq_expr) [ pass_statement ] ;
```
Monitors the property or sequence for coverage and reports statistics. The statement is executed when the property succeeds. Cover sequence reports all matches. Example:

```systemverilog
C1: cover property (@(event) a |-> b ##[2:5] c);
```

## Expect Statement

```systemverilog
expect (prop_expr) [ action_block ] ;
```
Blocks the current process until the property succeeds or fails. Example:

```systemverilog
expect( @(posedge clk) ##[1:10] top.TX_Monitor.data == value ) 
success = 1; 
else success = 0;
```

## Clock Expressions

```systemverilog
@( {{posedge | negedge} clock | expression} )
```
Declares an event or event expression to use for sampling assertion variable values. Multiple clocks, and clocks inferred from an always block containing only assertions, are supported. Examples:

```systemverilog
assert property @(posedge clk1) (a ##1 b) |=> @(posedge clk2) (c ##1 d)); 
endproperty

assert property ( @(posedge clk1) (a ##1 b) |=> @(posedge clk2) (c ##1 d) );

always @(posedge clk) begin 
assert property ( (a ##1 b) |=> (c ##1 d) ); 
assert property ( (a[*3]) |=> ~c ); 
cover property ( (a ##1 b ##1 c) |=> (d[*2:4]) ); 
end
```

## Default Clocking Blocks

```systemverilog
default clocking [clk_identifier] {identifier | clk_expression} ; 
clocking_items

end clocking default clocking clk_identifier
```
Specifies the clock or event that controls property evaluation. Example:

```systemverilog
default clocking master_clk @(posedge clk); 
property p4; 
(a |=> ##2 b); 
endproperty 
assert property (p4); 
endclocking
```

## Disable Clause

```systemverilog
disable iff (boolean_expr) 
default disable iff (boolean_expr)
```
Specifies a reset expression. Checking of the property is terminated asynchronously when the expression is true. Example:

```systemverilog
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

## Property Expressions

### |-> 

```systemverilog
sequence_expr |-> property_expr 
```
The property expression must be true in the last cycle that the sequence expression is true (overlapping). Example:

```systemverilog
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

###  |=> 

```systemverilog
sequence_expr |=> property_expr 
```
The property expression must be true in the first cycle after the sequence expression is true. Example:

```systemverilog
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

### and

```systemverilog
property_expr and property_expr 
```
Returns true if both property expressions are true. Example:

```systemverilog
@(c) v |=> (w ##1 @(d) x) and (y ##1 z)
```

### not

```systemverilog
not property_expr 
```
Returns the opposite of the value returned by the property_expr. Example:

```systemverilog
property abcd; 
@(posedge clk) a |-> not (b ##1 c ##1 d); 
endproperty
```

### if

```systemverilog
if (expression) property_expr1 [ else property_expr2] 
```
If expression is true, property_expr1 must hold; property_expr1 does not need to hold when expression is false. If expression is false, property_expr2 must hold, if it exists. Example:

```systemverilog
property P2; 
@ (negedge clk) if (a) b |=> c; else d |=> e; 
endproperty
```

## Sequence Operators

### and

```systemverilog
sequence_expr1 and sequence_expr2 
```
Both sequences must occur, but the end times of the operands can be different. Example:

```systemverilog
(a ##2 b) and (c ##2 d ##2 e) ;
```

### first_match

```systemverilog
first_match (sequence_expr[, seq_match_item])
```
Evaluation of one or more sequences stops when the first match is found. Example:

```systemverilog
sequence s1; 
first_match(a ##1 b[->1]:N] ## c); 
endsequence
```

### intersect

```systemverilog
sequence_expr1 intersect sequence_expr2 
```
Both sequences must occur, and the start and end times of the sequence expressions must be the same. Example:

```systemverilog
(a ##2 b) intersect (c ##2 d ##2 e)
```

### or

```systemverilog
sequence_expr1 or sequence_expr2 
```
At least one of the sequences must occur. Example:

```systemverilog
(b ##1 c) or (d[*1:2] ##1 e) or f[*2]
```

### throughout

```systemverilog
boolean_expr throughout sequence_expr 
```
A condition must hold true for the duration of a sequence. Example:

```systemverilog
(a ##2 b) throughout read_sequence
```

### within

```systemverilog
sequence_expr1 within sequence_expr2 
```
sequence_expr1 must match at some point within the timeframe of sequence_expr2. Example:

```systemverilog
(a ##2 b ##3 c) within write_enable
```

## Sequence Methods

```systemverilog
sequence_instance.[ ended|matched|triggered]
```
Identifies the endpoint of a sequence. Example:

```systemverilog
wait (AB.triggered) || BC.triggered); 
if (AB.triggered) $display("AB triggered");
```

## Cycle Delays

```systemverilog
##integral_number ##Identifier ##(constant_expression) ##[const_expr : const_expr] ##[const_expr : $]
```
Specifies the number of clock ticks from the current clock tick until the next specified behavior occurs. Example:

```systemverilog
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## Local Variables in Sequences and Properties

```systemverilog
(seq_expression {, seq_match_item}) [ repetition_op ] 
```
The seq_match_item is executed when seq_expression is matched. The match item can be a subroutine call. Example:

```systemverilog
sequence data_check; 
int x; 
a ##1 (!a, x=data_in) ##1 !b[*0:$] ##1 b && (data_out=x); 
endsequence
```

## Repetition

### Consecutive Repetition

```systemverilog
[* const_or_range_expression ]
```
Consecutive repetition. Example:

```systemverilog
(a[*2] ##2 b[*2]) |=> (d)
```

### Goto Repetition

```systemverilog
[-> const_or_range_expression ]
```
Goto repetition. Example:

```systemverilog
a ##1 b[->5] ##1 c
```

### Non-Consecutive Repetition

```systemverilog
[= const_or_range_expression ]
```
Non-consecutive repetition. Example:

```systemverilog
s1 |=> (b [=5] ##1 c)
```

## Shortcuts

- R[*] is the same as R[*0:$]
- ##[*] is the same as ##[0:$]
- R[+] is the same as R[*1:$]
- ##[+] is the same as ##[1:S]

## Assertion Severity Tasks

### Fatal

```systemverilog
$fatal ([ 0 | 1 | 2 , ] message [ , args ] ) ;
```
Fatal message task; messages can be strings or expressions. You can call this task from the action block of an assertion. Example:

```systemverilog
$fatal (0);
```

### Error, Warning, Info

```systemverilog
$error (message [ , args ] ) ; 
$warning (message [ , args ] ) ; 
$info (message [ , args ] ) ;
```
Non-fatal message tasks; messages can be strings or expressions. You can call these tasks from the action block of an assertion. Example:

```systemverilog
$error("Unsupported memory task command %b", m_task); 
$warning("Enable is set during non-read op: state=>%b", state);
```

## System Functions

### One Hot

```systemverilog
$onehot (bit_vector)
```
Returns true if one and only one bit of the expression is high. Example:

```systemverilog
property p1(Arg) 
@(posedge clk) $onehot(Arg); 
endproperty
```

### One Hot 0

```systemverilog
$onehot0 (bit_vector)
```
Returns true if no more than one bit of the expression is high. Example:

```systemverilog
property p2(Arg) 
@(posedge clk) $onehot0(Arg); 
endproperty
```

### Is Unknown

```systemverilog
$isunknown (bit_vector)
```
Returns true if any bit of the expression is X or Z. Example:

```systemverilog
property p3(Arg) 
@(posedge clk) $isunknown(Arg); 
endproperty
```

### Count Ones

```systemverilog
$countones (bit_vector)
```
Returns the number of bits in a vector that have the value 1. Example:

```systemverilog
property p4(Arg) 
@(posedge clk) $countones(Arg) == 4; 
endproperty
```

## Sampled-Value Functions

### Sampled

```systemverilog
$sampled(expression)
```
Returns the sampled value of the expression at the current clock cycle. Example:

```systemverilog
property propA 
@(posedge clk) (a ##1 b); 
endproperty 
p1: assert (propA) 
$display("%m passed"); 
else $warning("a == %s; b == %s", $sampled(test.inst.a), $sampled(test.inst.b));
```

### Rose

```systemverilog
$rose(expression)
```
Returns true if the sampled value of expression changed to 1 during the current clock cycle. Example:

```systemverilog
Example: (a ##1 b) |-> $rose(test.inst.sig4);
```

### Fell

```systemverilog
$fell(expression)
```
Returns true if the sampled value of expression changed to 0 during the current clock cycle. Example:

```systemverilog
(a ##1 b) |-> $fell(test.inst.c);
```

### Stable

```systemverilog
$stable(expression)
```
Returns true if the sampled value of expression remained the same during the current clock cycle. Example:

```systemverilog
(a ##1 b) |-> $stable(test.inst.c);
```

### Past

```systemverilog
$past(expression [ , n_cycles] )
```
Returns the sampled value of expression at the previous clock cycle or the specified number of clock ticks in the past. Example:

```systemverilog
(a == $past(test.inst.c, 5)
```

## Assertion-Control System Tasks

```systemverilog
$assertoff [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$asserton [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$assertkill [ ( levels [ , list_of_mods_or_assns ] ) ] ;
```
Controls assertion checking during simulation. Example:

```systemverilog
$assertoff (0, top.mod1, top.mod2.net1);
```
