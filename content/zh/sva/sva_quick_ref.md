
---
weight: 2
title: "SVA 快速参考手册"
description: "SystemVerilog Assertion（SVA） 快速参考手册；SVA Quick Reference"

---

**注意**：该 SVA 快速参考手册目前支持 IEEE 1800-2005 标准。

## 0. 绑定（Binding）

`bind target bind_obj [ (params)] bind_inst (ports) ;`

将 SystemVerilog 模块或接口附加到 Verilog 模块或接口实例，或 VHDL 实体/架构。支持多个目标。示例：

```systemverilog
bind fifo fifo_full v1(clk,empty,full); 
bind top.dut.fifo1 fifo_full v2(clk,empty,full); 
bind fifo:fifo1,fifo2 fifo_full v3(clk,empty,full);
```

## 1. 立即断言（Immediate Assertions）

`[ label : ] assert (boolean_expr) [ action_block ] ;`

在执行过程性代码时测试表达式。示例：

```systemverilog
enable_set_during_read_op_only : assert (state >= `start_read && state <= `finish_read); 
    else $warning("Enable set when state => %b", state);
```

## 2. 声明（Declarations）

### 2.1 序列（Sequence）

```systemverilog
sequence identifier [ argument_list ] ;
    sequence_expr [ seq_op sequence_expr ] ... ; 
endsequence [ : identifier ] 
````

声明一个可以在属性声明中使用的序列表达式。允许使用局部变量。示例：

```systemverilog
sequence BusReq (bit REQ=0, bit ACK=0); 
    REQ ##[1:3] ACK; 
endsequence
```

### 2.2 属性（Property）

```systemverilog
property identifier [ argument_list ] ;
    [ clock_expr ] [ disable_clause ] property_expr ; 
endproperty [ : identifier ] 
```
声明在仿真过程中要验证的 condition 或 sequence。允许使用局部变量。示例：

```systemverilog
property P6 (bit AA, BB=`true, EN=1); 
    @(negedge clk) 
    EN -> (BB ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

`[ identifier: ] [ (argument_list) ]`

创建属性声明的实例。示例：

```systemverilog
property P1;
    @(event) a && b ##1 !a && !b;
endproperty
property P2;
    @(posedge clk) rst |-> P1;
endproperty
```

## 3. 指令（Directives）

### 3.1 断言属性（Assert Property）

`[ label : ] assert property (prop_expr) [ action_block ] ;`

在验证过程中检查属性。示例：

```systemverilog
property P5 (AA); 
    @(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty 
assert property (P5(a));
```

### 3.2 假设属性（Assume Property）

`[label:] assume property (prop_expr) [ action_block ] ;`

限制验证过程中考虑的输入。在仿真中，处理方式类似于断言。示例：

```systemverilog
A1: assume (@(ena) !rst);
```

### 3.3 覆盖属性（Cover Property）

`[label:] cover property (prop_expr) [ pass_statement ] ; `   
`[label:] cover sequence (seq_expr) [ pass_statement ] ;`


监控属性或序列的覆盖率并报告统计信息。当属性成功时，执行语句。覆盖序列报告所有匹配项。示例：

```systemverilog
C1: cover property (@(event) a |-> b ##[2:5] c);
```

## 4. 期望语句（Expect Statement）

`expect (prop_expr) [ action_block ] ;`

阻塞当前进程，直到属性成功或失败。示例：

```systemverilog
expect( @(posedge clk) ##[1:10] top.TX_Monitor.data == value ) 
    success = 1; 
else success = 0;
```

## 5. 时钟表达式（Clock Expressions）

`@( {{posedge | negedge} clock | expression} )`

声明事件或事件表达式，用于采样断言变量的值。支持多个时钟，以及从仅包含断言的 always 块推断的时钟。示例：

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

## 6. 默认时钟块（Default Clocking Blocks）

```systemverilog
default clocking [clk_identifier] {identifier | clk_expression} ; 
    clocking_items
end clocking 
default clocking clk_identifier
```

指定控制属性评估的时钟或事件。示例：

```systemverilog
default clocking master_clk @(posedge clk); 
    property p4; 
        (a |=> ##2 b); 
    endproperty 
    assert property (p4); 
endclocking
```

## 7. 禁用子句（Disable Clause）

```systemverilog
disable iff (boolean_expr) 
default disable iff (boolean_expr)
```
指定一个复位表达式。当表达式为真时，属性检查异步终止。示例：

```systemverilog
property P4; 
    @(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

## 8. 属性表达式（Property Expressions）

### 8.1 |->

`sequence_expr |-> property_expr `

属性表达式必须在序列表达式为真的最后一个周期内为真（重叠）。示例：

```systemverilog
property P4; 
    @(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

### 8.2 |=>

`sequence_expr |=> property_expr `

属性表达式必须在序列表达式为真后的第一个周期内为真。示例：

```systemverilog
property property P5 (AA); 
    @(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

### 8.3 and

`property_expr and property_expr `

如果两个属性表达式都为真，则返回真。示例：

```systemverilog
@(c) v |=> (w ##1 @(d) x) and (y ##1 z)
```

### 8.4 not

`not property_expr `

返回属性表达式的反值。示例：

```systemverilog
property abcd; 
    @(posedge clk) a |-> not (b ##1 c ##1 d); 
endproperty
```

### 8.5 if

`if (expression) property_expr1 [ else property_expr2] `

如果表达式为真，则 property_expr1 必须成立；如果表达式为假，则 property_expr2 必须成立（如果存在）。示例：

```systemverilog
property P2; 
@ (negedge clk) if (a) b |=> c; else d |=> e; 
endproperty
```

## 9. 序列操作符（Sequence Operators）

### 9.1 and

`sequence_expr1 and sequence_expr2 `

两个序列必须都发生，但操作数的结束时间可以不同。示例：

```systemverilog
(a ##2 b) and (c ##2 d ##2 e) ;
```

### 9.2 first_match

`first_match (sequence_expr[, seq_match_item])`

一旦找到第一次匹配，就停止对一个或多个序列的评估。示例：

```systemverilog
sequence s1; 
first_match(a ##1 b[->1]:N] ## c); 
endsequence
```

### 9.3 intersect

`sequence_expr1 intersect sequence_expr2 `

两个序列必须都发生，且序列表达式的起始和结束时间必须相同。示例：

```systemverilog
(a ##2 b) intersect (c ##2 d ##2 e)
```

### 9.4 or

`sequence_expr1 or sequence_expr2 `

至少有一个序列必须发生。示例：

```systemverilog
(b ##1 c) or (d[*1:2] ##1 e) or f[*2]
```

### 9.5 throughout

`boolean_expr throughout sequence_expr `

条件必须在整个序列的持续时间内成立。示例：

```systemverilog
(a ##2 b) throughout read_sequence
```

### 9.6 within

`sequence_expr1 within sequence_expr2 `

sequence_expr1 必须在 sequence_expr2 的时间范围内匹配某一时刻。示例：

```systemverilog
(a ##2 b ##3 c) within write_enable
```

## 10. 序列方法（Sequence Methods）

` sequence_instance.[ ended|matched|triggered]`

标识序列的终点。示例：

```systemverilog
wait ((AB.triggered) || BC.triggered); 
    if (AB.triggered) $display("AB triggered");
```

## 11. 周期延迟（Cycle Delays）

`##integral_number `
`##Identifier `
`##(constant_expression) `
`##[const_expr : const_expr]`
`##[const_expr : $]`

指定从当前时钟周期到下一个指定行为发生的时钟周期数。示例：

```systemverilog
property property P5 (AA); 
    @(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## 12. 序列和属性中的局部变量（Local Variables in Sequences and Properties）

`(seq_expression {, seq_match_item}) [ repetition_op ] `

当 seq_expression 匹配时，执行 seq_match_item。匹配项可以是子程序调用。示例：

```systemverilog
sequence data_check; 
int x; 
a ##1 (!a, x=data_in) ##1 !b[*0:$] ##1 b && (data_out=x); 
endsequence
```

## 13. 重复（Repetition）

### 13.1 连续重复（Consecutive Repetition）

`[* const_or_range_expression ] `

连续重复。示例：

```systemverilog
(a[*2] ##2 b[*2]) |=> (d)
```

### 13.2 跳转重复（Goto Repetition）

`[-> const_or_range_expression ]`

跳转重复。示例：

```systemverilog
a ##1 b[->5] ##1 c
```

### 13.3 非连续重复（Non-Consecutive Repetition）

`[= const_or_range_expression ]`

非连续重复。示例：

```systemverilog
s1 |=> (b [=5] ##1 c)
```

## 14. 快捷方式（Shortcuts）

- R[*] 等同于 R[*0:$]
- ##[*] 等同于 ##[0:$]
- R[+] 等同于 R[*1:$]
- ##[+] 等同于 ##[1:S]

## 15. 断言严重性任务（Assertion Severity Tasks）

### 15.1 Fatal

`$fatal ([ 0 | 1 | 2 , ] message [ , args ] ) ;`

致命消息任务；消息可以是字符串或表达式。您可以从断言的操作块调用此任务。示例：

```systemverilog
$fatal (0);
```

### 15.2 错误、警告、信息（Error, Warning, Info）

`$error (message [ , args ] ) ; `  
`$warning (message [ , args ] ) ; `  
`$info (message [ , args ] ) ;`  

非致命消息任务；消息可以是字符串或表达式。您可以从断言的操作块调用这些任务。示例：

```systemverilog
$error("Unsupported memory task command %b", m_task); 
$warning("Enable is set during non-read op: state=>%b", state);
```

## 16. 系统函数（System Functions）

### 16.1 onehot

`$onehot (bit_vector)`

如果表达式中只有一个位为高电平，则返回真。示例：

```systemverilog
property p1(Arg) 
@(posedge clk) $onehot(Arg); 
endproperty
```

### 16.2 onehot0

`$onehot0 (bit_vector)`

如果表达式中至多只有一个位为高电平，则返回真。示例：

```systemverilog
property p2(Arg) 
@(posedge clk) $onehot0(Arg); 
endproperty
```

### 16.3 isunknown

`$isunknown (bit_vector)`

如果表达式中任何一位为 X 或 Z，则返回真。示例：

```systemverilog
property p3(Arg) 
@(posedge clk) $isunknown(Arg); 
endproperty
```

### 16.4 countones

`$countones (bit_vector)`

返回向量中值为 1 的位数。示例：

```systemverilog
property p4(Arg) 
@(posedge clk) $countones(Arg) == 4; 
endproperty
```

## 17. 采样值函数（Sampled-Value Functions）

### 17.1 sampled

`$sampled(expression)`

返回表达式在当前时钟周期的采样值。示例：

```systemverilog
property propA 
@(posedge clk) (a ##1 b); 
endproperty 
p1: assert (propA) 
$display("%m passed"); 
else $warning("a == %s; b == %s", $sampled(test.inst.a), $sampled(test.inst.b));
```

### 17.2 rose

`$rose(expression)`

如果表达式的采样值在当前时钟周期改变为 1，则返回真。示例：

```systemverilog
Example: (a ##1 b) |-> $rose(test.inst.sig4);
```

### 17.3 fell

`$fell(expression)`

如果表达式的采样值在当前时钟周期改变为 0，则返回真。示例：

```systemverilog
(a ##1 b) |-> $fell(test.inst.c);
```

### 17.4 stable

`$stable(expression)`

如果表达式的采样值在当前时钟周期内保持不变，则返回真。示例：

```systemverilog
(a ##1 b) |-> $stable(test.inst.c);
```

### 17.5 past

`$past(expression [ , n_cycles] )`

返回表达式在上一个时钟周期或指定时钟周期数之前的采样值。示例：

```systemverilog
(a == $past(test.inst.c, 5)
```

## 18. 断言控制系统任务（Assertion-Control System Tasks）

`$assertoff [ ( levels [ , list_of_mods_or_assns ] ) ] ; `
`$asserton [ ( levels [ , list_of_mods_or_assns ] ) ] ; `
`$assertkill [ ( levels [ , list_of_mods_or_assns ] ) ] ;`


控制仿真过程中的断言检查。示例：

```systemverilog
$assertoff (0, top.mod1, top.mod2.net1);
```