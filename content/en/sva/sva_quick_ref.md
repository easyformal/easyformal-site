
---
weight: 2
title: "SystemVerilog Assertion Quick Reference"
description: "SystemVerilog Assertion Quick Reference；SVA Quick Reference"

---

**Note:** Numbers in parentheses indicate the section in the IEEE 1800-2005 Standard for SystemVerilog for the given construct.

## Binding

```plaintext
bind target bind_obj [ (params)] bind_inst (ports) ;
```
Attaches a SystemVerilog module or interface to a Verilog module or interface instance, or to a VHDL entity/architecture. Multiple targets supported. Example:

```plaintext
bind fifo fifo_full v1(clk,empty,full); 
bind top.dut.fifo1 fifo_full v2(clk,empty,full); 
bind fifo:fifo1,fifo2 fifo_full v3(clk,empty,full);
```

## Immediate Assertions

```plaintext
[ label : ] assert (boolean_expr) [ action_block ] ;
```
Tests an expression when the statement is executed in the procedural code. Example:

```plaintext
enable_set_during_read_op_only : assert (state >= ‘start_read && state <= ‘finish_read); 
else $warning("Enable set when state => %b", state);
```

## Declarations

### Sequence

```plaintext
sequence identifier [ argument_list ] ;
sequence_expr [ seq_op sequence_expr ] ... ; 
endsequence [ : identifier ] 
```
Declares a sequence expression that can be used in property declarations. Local variables are permitted. Example:

```plaintext
sequence BusReq (bit REQ=0, bit ACK=0); 
REQ ##[1:3] ACK; 
endsequence
```

### Property

```plaintext
property identifier [ argument_list ] ;
[ clock_expr ] [ disable_clause ] property_expr ; 
endproperty [ : identifier ] 
```
Declares a condition or sequence to be verified during simulation. Local variables are permitted. Example:

```plaintext
property P6 (bit AA, BB=‘true, EN=1); 
@(negedge clk) EN -> (BB ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## Directives

### Assert Property

```plaintext
[ label : ] assert property (prop_expr) [ action_block ] ;
```
Checks a property during verification. Example:

```plaintext
property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty 
assert property (P5(a));
```

### Assume Property

```plaintext
[label:] assume property (prop_expr) [ action_block ] ;
```
Constrains the inputs considered for the property during verification. In simulation, treated like assert. Example:

```plaintext
A1: assume (@(ena) !rst);
```

### Cover Property

```plaintext
[label:] cover property (prop_expr) [ pass_statement ] ; 
[label:] cover sequence (seq_expr) [ pass_statement ] ;
```
Monitors the property or sequence for coverage and reports statistics. The statement is executed when the property succeeds. Cover sequence reports all matches. Example:

```plaintext
C1: cover property (@(event) a |-> b ##[2:5] c);
```

## Expect Statement

```plaintext
expect (prop_expr) [ action_block ] ;
```
Blocks the current process until the property succeeds or fails. Example:

```plaintext
expect( @(posedge clk) ##[1:10] top.TX_Monitor.data == value ) 
success = 1; 
else success = 0;
```

## Clock Expressions

```plaintext
@( {{posedge | negedge} clock | expression} )
```
Declares an event or event expression to use for sampling assertion variable values. Multiple clocks, and clocks inferred from an always block containing only assertions, are supported. Examples:

```plaintext
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

```plaintext
default clocking [clk_identifier] {identifier | clk_expression} ; 
clocking_items

end clocking default clocking clk_identifier
```
Specifies the clock or event that controls property evaluation. Example:

```plaintext
default clocking master_clk @(posedge clk); 
property p4; 
(a |=> ##2 b); 
endproperty 
assert property (p4); 
endclocking
```

## Disable Clause

```plaintext
disable iff (boolean_expr) 
default disable iff (boolean_expr)
```
Specifies a reset expression. Checking of the property is terminated asynchronously when the expression is true. Example:

```plaintext
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

## Property Expressions

### Sequence to Property

```plaintext
sequence_expr |-> property_expr 
```
The property expression must be true in the last cycle that the sequence expression is true (overlapping). Example:

```plaintext
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

### Sequence Implies Property

```plaintext
sequence_expr |=> property_expr 
```
The property expression must be true in the first cycle after the sequence expression is true. Example:

```plaintext
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

### And Property

```plaintext
property_expr and property_expr 
```
Returns true if both property expressions are true. Example:

```plaintext
@(c) v |=> (w ##1 @(d) x) and (y ##1 z)
```

### Not Property

```plaintext
not property_expr 
```
Returns the opposite of the value returned by the property_expr. Example:

```plaintext
property abcd; 
@(posedge clk) a |-> not (b ##1 c ##1 d); 
endproperty
```

### If Property

```plaintext
if (expression) property_expr1 [ else property_expr2] 
```
If expression is true, property_expr1 must hold; property_expr1 does not need to hold when expression is false. If expression is false, property_expr2 must hold, if it exists. Example:

```plaintext
property P2; 
@ (negedge clk) if (a) b |=> c; else d |=> e; 
endproperty
```

## Sequence Operators

### And Sequence

```plaintext
sequence_expr1 and sequence_expr2 
```
Both sequences must occur, but the end times of the operands can be different. Example:

```plaintext
(a ##2 b) and (c ##2 d ##2 e) ;
```

### First Match

```plaintext
first_match (sequence_expr[, seq_match_item])
```
Evaluation of one or more sequences stops when the first match is found. Example:

```plaintext
sequence s1; 
first_match(a ##1 b[->1]:N] ## c); 
endsequence
```

### Intersect Sequence

```plaintext
sequence_expr1 intersect sequence_expr2 
```
Both sequences must occur, and the start and end times of the sequence expressions must be the same. Example:

```plaintext
(a ##2 b) intersect (c ##2 d ##2 e)
```

### Or Sequence

```plaintext
sequence_expr1 or sequence_expr2 
```
At least one of the sequences must occur. Example:

```plaintext
(b ##1 c) or (d[*1:2] ##1 e) or f[*2]
```

### Throughout

```plaintext
boolean_expr throughout sequence_expr 
```
A condition must hold true for the duration of a sequence. Example:

```plaintext
(a ##2 b) throughout read_sequence
```

### Within

```plaintext
sequence_expr1 within sequence_expr2 
```
sequence_expr1 must match at some point within the timeframe of sequence_expr2. Example:

```plaintext
(a ##2 b ##3 c) within write_enable
```

## Sequence Methods

```plaintext
sequence_instance.[ ended|matched|triggered]
```
Identifies the endpoint of a sequence. Example:

```plaintext
wait (AB.triggered) || BC.triggered); 
if (AB.triggered) $display("AB triggered");
```

## Cycle Delays

```plaintext
##integral_number ##Identifier ##(constant_expression) ##[const_expr : const_expr] ##[const_expr : $]
```
Specifies the number of clock ticks from the current clock tick until the next specified behavior occurs. Example:

```plaintext
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## Local Variables in Sequences and Properties

```plaintext
(seq_expression {, seq_match_item}) [ repetition_op ] 
```
The seq_match_item is executed when seq_expression is matched. The match item can be a subroutine call. Example:

```plaintext
sequence data_check; 
int x; 
a ##1 (!a, x=data_in) ##1 !b[*0:$] ##1 b && (data_out=x); 
endsequence
```

## Repetition

### Consecutive Repetition

```plaintext
[* const_or_range_expression ]
```
Consecutive repetition. Example:

```plaintext
(a[*2] ##2 b[*2]) |=> (d)
```

### Goto Repetition

```plaintext
[-> const_or_range_expression ]
```
Goto repetition. Example:

```plaintext
a ##1 b[->5] ##1 c
```

### Non-Consecutive Repetition

```plaintext
[= const_or_range_expression ]
```
Non-consecutive repetition. Example:

```plaintext
s1 |=> (b [=5] ##1 c)
```

## Shortcuts

- R[*] is the same as R[*0:$]
- ##[*] is the same as ##[0:$]
- R[+] is the same as R[*1:$]
- ##[+] is the same as ##[1:S]

## Assertion Severity Tasks

### Fatal

```plaintext
$fatal ([ 0 | 1 | 2 , ] message [ , args ] ) ;
```
Fatal message task; messages can be strings or expressions. You can call this task from the action block of an assertion. Example:

```plaintext
$fatal (0);
```

### Error, Warning, Info

```plaintext
$error (message [ , args ] ) ; 
$warning (message [ , args ] ) ; 
$info (message [ , args ] ) ;
```
Non-fatal message tasks; messages can be strings or expressions. You can call these tasks from the action block of an assertion. Example:

```plaintext
$error("Unsupported memory task command %b", m_task); 
$warning("Enable is set during non-read op: state=>%b", state);
```

## System Functions

### One Hot

```plaintext
$onehot (bit_vector)
```
Returns true if one and only one bit of the expression is high. Example:

```plaintext
property p1(Arg) 
@(posedge clk) $onehot(Arg); 
endproperty
```

### One Hot 0

```plaintext
$onehot0 (bit_vector)
```
Returns true if no more than one bit of the expression is high. Example:

```plaintext
property p2(Arg) 
@(posedge clk) $onehot0(Arg); 
endproperty
```

### Is Unknown

```plaintext
$isunknown (bit_vector)
```
Returns true if any bit of the expression is X or Z. Example:

```plaintext
property p3(Arg) 
@(posedge clk) $isunknown(Arg); 
endproperty
```

### Count Ones

```plaintext
$countones (bit_vector)
```
Returns the number of bits in a vector that have the value 1. Example:

```plaintext
property p4(Arg) 
@(posedge clk) $countones(Arg) == 4; 
endproperty
```

## Sampled-Value Functions

### Sampled

```plaintext
$sampled(expression)
```
Returns the sampled value of the expression at the current clock cycle. Example:

```plaintext
property propA 
@(posedge clk) (a ##1 b); 
endproperty 
p1: assert (propA) 
$display("%m passed"); 
else $warning("a == %s; b == %s", $sampled(test.inst.a), $sampled(test.inst.b));
```

### Rose

```plaintext
$rose(expression)
```
Returns true if the sampled value of expression changed to 1 during the current clock cycle. Example:

```plaintext
Example: (a ##1 b) |-> $rose(test.inst.sig4);
```

### Fell

```plaintext
$fell(expression)
```
Returns true if the sampled value of expression changed to 0 during the current clock cycle. Example:

```plaintext
(a ##1 b) |-> $fell(test.inst.c);
```

### Stable

```plaintext
$stable(expression)
```
Returns true if the sampled value of expression remained the same during the current clock cycle. Example:

```plaintext
(a ##1 b) |-> $stable(test.inst.c);
```

### Past

```plaintext
$past(expression [ , n_cycles] )
```
Returns the sampled value of expression at the previous clock cycle or the specified number of clock ticks in the past. Example:

```plaintext
(a == $past(test.inst.c, 5)
```

## Assertion-Control System Tasks

```plaintext
$assertoff [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$asserton [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$assertkill [ ( levels [ , list_of_mods_or_assns ] ) ] ;
```
Controls assertion checking during simulation. Example:

```plaintext
$assertoff (0, top.mod1, top.mod2.net1);
```
