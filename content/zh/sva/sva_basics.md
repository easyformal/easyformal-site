
---
weight: 3
title: "SVA 快速入门教程(TBD)"
description: "SystemVerilog Assertion（SVA） 快速入门教程；SVA Quick Tutorial"
---

### 1. Introduction

- Assertions are primarily used to validate the behavior of a design
- Piece of verification code that monitors a design implementation for compliance with the specifications
- Directive to a verification tool that the tool should attempt to prove/assume/count a given property using formal methods
- Capture the design intent more formally and find specification error earlier
- Find more bugs and source of the bugs faster
- Encourage measurement of function coverage and assertion coverage
- Re-use checks throughout life-cycle, strength regression testing

### 2.  Benefits of Assertions

- Improves observability of the design
    - Using assertions one can create unlimited number of observation points any where in the design
    - Enables internal state, datapath and error pre-condition coverage analysis
- Improves debugging of the design
    - Assertion help capture the improper functionality of the DUT at or near the source of the problem thereby reducing the debug time
    - With failure of assertion one can debug by considering only the dependent signals or auxiliary code associated to the specific assertion in question
    - Assertion also helps to capture bugs, which do not propagate to the output
- Improves the documentation of the Design
    - Assertions capture the specification of the Design. The spec is translated into an executable form in the form of assertions, assumptions, constraints, restrictions. The specifications are checked during the entire development and validation process
    - Assumptions in assertions capturing the design assumptions continuously verify whether the assumptions hold true throughout the simulation
    - Assertions always capture the specification in concise form which is not ambiguous i.e., assertions are the testable form of requirements
    - Assertions go along with the design and can also be enabled at SOC level
- Assertion can be used to provide functional coverage.
    - Functional coverage is provided by cover property.
    - Cover property is to monitor the property evaluation for functional coverage. It covers the properties/sequences that we have specified.
    - We can monitor whether a particular verification node is exercised or not as per the specification.
    - Can be written for:
        - Low-level functionality coverage inside a block.
        - High-level functionality coverage at interface level.
- Can use these assertions in formal analysis.
    - Formal analysis uses sophisticated algorithms to prove or disprove that a design behaves as desired for all the possible operating states.One limitation is that it is effective only in block level not at full chip or SOC level.
    - Desire behavior is not expressed in a traditional test bench, but rather as a set of assertions. Formal analysis does not require test vectors.
    - With Formal analysis many bugs can be found quickly and very easily in the Design process without the need to develop large sets of test vectors.

### 3. Where SVA can reside? 

![sva_reside](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/sva_reside.png)

### 4. Who writes Assertions? 

- White-Box Verification
    - Inserted by design engineers
    - Block Interfaces
    - Internal signals
- Black-box Verification
  - Inserted by
    - IP Providers
    - Verification Engineers
  - External interfaces
  - End-to-end properties 

### 5. SystemVerilog Assertion Example 

A concise description of complex behaviour: After request is asserted, acknowledge must come 1 to 3 cycles later.

![sva_example](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/sva_example.png)

### 6. Types of SVA

- Immediate Assertions
- Concurrent Assertions

### 7. Immediate Assertions

- Immediate assertions = instructions to a simulator.
- Follows simulations event semantics.
- Appears as a procedural statement, executed like a statement in a procedural block.
- Syntax: assert (expression) pass_statement [else fail_statement].
- The statement is non-temporal and treated as a condition in if statement.
- The else block is optional, however it allows registering severity of assertion failure.
- Severity System tasks:
   - $fatal: run time fatal, terminates simulation.
   - $error: run time error (default).
   - $warning: run time warning, can be suppressed by command-line option.
   - $info: failure carries no specific severity, can be suppressed.
- All severity system tasks print the severity level, the file name and line
number, the hierarchical name or scope, simulation time, etc. 
- Example: 
```systemverilog
always @ (posedge clk) begin:checkResults
    assert ( output == expected ) okCount++;
    else begin
        $error(“Output is incorrect”);
        errCount++;
    end
end 
```

### 8. Concurrent Assertions

- Concurrent assertions = instructions to verification tools.
- Based on clock semantics. Evaluated on the clock edge.
- Values of the variables used in evaluation are the sampled values.
- Detects behavior over a period of time.
- Ability to specify behavior over time. So these are called temporal expressions.
- Assertions occur both in procedural block and a module.
- example:

```systemverilog 
assert property (
    @(posedge clk) a ##1 b |-> d ##1 e
); 
```

#### 8.1 Layers of Concurrent Assertion

-  Make the sequence
-  Evaluate the sequence
-  Define a property for sequence with pass fail
-  Property asserted with a specific block (e.g.: Illegal sequence, measuring coverage…)

#### 8.1.1 Boolean expression layer

-  Elementary layer of Concurrent assertion
-  Evaluates Boolean expression to be either TRUE or FALSE
-  Occur in the following of concurrent properties
-  In the Sequences used to build properties
-  In top level disable iff claues

`assert property ( @(posedge clk) disable iff (a && $rose(b, posedge clk)) trigger |=> test_expr;`

-  restrictions on the type of variables shortreal, real and realtime
    -  string
    -  event
    -  chandle
    -  class
    -  associative array
    -  dynamic array
-  Functions in expressions should be automatic
-  Variable in expression bust be static design variable
-  Sampling a variable in concurrent assertions

![concurrent_assertion](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/concurrent_assertion.png)

-  The value of signal req is low at clocks 1. At clock tick 2, the value is sampled as high and remains high until clock tick 4. The sampled value req at clock tick 4 is low and remains low until clock tick 6 
-  Notice that, at clock tick 5, the simulation value transitions to high. However, the sampled value is low 

#### 8.1.1 Sequence layer

build on top of Boolean expression layer, and describe sequence made of series of events and other sequences

    -  Linear sequence: absolute timing relation is known
    -  Nonlinear sequence
      -  multiple events trigger a sequence and not time dependant
      -  multiple sequences interact with and control one another
    -  Sequence block
      -  Define one or more sequences
      -  Syntax:
```
        sequence identifier (formal_argument_list);
            variable declarations
            sequence_spec
        endsequence
```
      -  Example:
```
sequence seq1 
    ~reset##5 req; 
endsequence 
```
```
sequence seq2 
    req##2 ack;
endsequence
```
```
sequence seq3
    seq1##2 ack
endsequence
```
    -  Usage: sequence can be instantiated in any of the following
blocks
      -  A module
      -  An interface block
      -  A program block

      - A clocking block
      - A package
      - A compilation unit scope
    - ## delay operator: used to join expression consisting of events.
      - Usage:
        - ## integral_number
        - identifier
        - ## (constant_expression)
        - ## [cycle_delay_const_range_expression]
      - The operator ## can be used multiple times within the same
chain. E.g., a ##1 b ##2 c ##3 d
      - You can indefinitely increase the length of a chain of events
using ## and 1'b1. The example below extends the previous
chain of events by 50 clocks. E.g., a ##1 b ##2 c ##3 d
##50 1'b1
      - Sequence overlap indicates b starts on the same clock when
a ends: a ##0 b
      - Sequence concatenation means b starts one clock after a
ends: a ##1 b
      - You can use an integer variable in place of the delay. E.g., a
##delay b
      - The following means b completes 2 clock ticks after a
completes (regardless of when b starts): a ##2 b.ended
      - You can specify a range of absolute delays too. E.g., a
##[1:4] b. You can also use a range of variable delays. E.g.,
a ##[delay1:delay2] b
      - The symbol $ in a delay range indicates that a signal or
event will 'eventually' occur. E.g., a ##[delay1:$] b
    - Sequence and clock
      - Implied clock
```
sequence seq1
    ~reset##5 req;
endsequence
```
      - Using clock inside a sequence
```      
sequence Sequence3;
    @(posedge clk_1) // clock name is clk_1
    s1 ##2 s2; // two sequences
endsequence
```
    - Sequence operations
![sequence_oper](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/sequence_oper.png)
      - Repetition operators
        - There are three types of repetition operators.
          - Consecutive Repetition Operator [* ]
          - Non-consecutive Repetition Operator [= ]
          - Goto Repetition Operator [-> ]

