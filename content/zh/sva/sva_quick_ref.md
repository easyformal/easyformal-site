
---
weight: 2
title: "SystemVerilog Assertion 快速参考手册（更新中）"
description: "SystemVerilog Assertion 快速参考手册；SVA Quick Reference"

---

**注意：**该 SVA 快速参考手册目前支持 IEEE 1800-2005 标准。

## 绑定（Binding）

```plaintext
bind target bind_obj [ (params)] bind_inst (ports) ;
```
将 SystemVerilog 模块或接口附加到 Verilog 模块或接口实例，或 VHDL 实体/架构。支持多个目标。示例：

```plaintext
bind fifo fifo_full v1(clk,empty,full); 
bind top.dut.fifo1 fifo_full v2(clk,empty,full); 
bind fifo:fifo1,fifo2 fifo_full v3(clk,empty,full);
```

## 立即断言（Immediate Assertions）

```plaintext
[ label : ] assert (boolean_expr) [ action_block ] ;
```
在执行过程性代码时测试表达式。示例：

```plaintext
enable_set_during_read_op_only : assert (state >= ‘start_read && state <= ‘finish_read); 
else $warning("Enable set when state => %b", state);
```

## 声明（Declarations）

### 序列（Sequence）

```plaintext
sequence identifier [ argument_list ] ;
sequence_expr [ seq_op sequence_expr ] ... ; 
endsequence [ : identifier ] 
```
声明一个可以在属性声明中使用的序列表达式。允许使用局部变量。示例：

```plaintext
sequence BusReq (bit REQ=0, bit ACK=0); 
REQ ##[1:3] ACK; 
endsequence
```

### 属性（Property）

```plaintext
property identifier [ argument_list ] ;
[ clock_expr ] [ disable_clause ] property_expr ; 
endproperty [ : identifier ] 
```
声明在仿真过程中要验证的条件或序列。允许使用局部变量。示例：

```plaintext
property P6 (bit AA, BB=‘true, EN=1); 
@(negedge clk) EN -> (BB ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## 指令（Directives）

### 断言属性（Assert Property）

```plaintext
[ label : ] assert property (prop_expr) [ action_block ] ;
```
在验证过程中检查属性。示例：

```plaintext
property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty 
assert property (P5(a));
```

### 假设属性（Assume Property）

```plaintext
[label:] assume property (prop_expr) [ action_block ] ;
```
限制验证过程中考虑的输入。在仿真中，处理方式类似于断言。示例：

```plaintext
A1: assume (@(ena) !rst);
```

### 覆盖属性（Cover Property）

```plaintext
[label:] cover property (prop_expr) [ pass_statement ] ; 
[label:] cover sequence (seq_expr) [ pass_statement ] ;
```
监控属性或序列的覆盖率并报告统计信息。当属性成功时，执行语句。覆盖序列报告所有匹配项。示例：

```plaintext
C1: cover property (@(event) a |-> b ##[2:5] c);
```

## 期望语句（Expect Statement）

```plaintext
expect (prop_expr) [ action_block ] ;
```
阻塞当前进程，直到属性成功或失败。示例：

```plaintext
expect( @(posedge clk) ##[1:10] top.TX_Monitor.data == value ) 
success = 1; 
else success = 0;
```

## 时钟表达式（Clock Expressions）

```plaintext
@( {{posedge | negedge} clock | expression} )
```
声明事件或事件表达式，用于采样断言变量的值。支持多个时钟（17.12），以及从仅包含断言的 always 块推断的时钟。示例：

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

## 默认时钟块（Default Clocking Blocks）

```plaintext
default clocking [clk_identifier] {identifier | clk_expression} ; 
clocking_items

end clocking default clocking clk_identifier
```
指定控制属性评估的时钟或事件。示例：

```plaintext
default clocking master_clk @(posedge clk); 
property p4; 
(a |=> ##2 b); 
endproperty 
assert property (p4); 
endclocking
```

## 禁用子句（Disable Clause）

```plaintext
disable iff (boolean_expr) 
default disable iff (boolean_expr)
```
指定一个复位表达式。当表达式为真时，属性检查异步终止。示例：

```plaintext
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

## 属性表达式（Property Expressions）

### 序列到属性（Sequence to Property）

```plaintext
sequence_expr |-> property_expr 
```
属性表达式必须在序列表达式为真的最后一个周期内为真（重叠）。示例：

```plaintext
property P4; 
@(negedge clk) disable iff (rst) (c) |-> (##[max-1:$] d); 
endproperty
```

### 序列意味着属性（Sequence Implies Property）

```plaintext
sequence_expr |=> property_expr 
```
属性表达式必须在序列表达式为真后的第一个周期内为真。示例：

```plaintext
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

### 与属性（And Property）

```plaintext
property_expr and property_expr 
```
如果两个属性表达式都为真，则返回真。示例：

```plaintext
@(c) v |=> (w ##1 @(d) x) and (y ##1 z)
```

### 非属性（Not Property）

```plaintext
not property_expr 
```
返回属性表达式的反值。示例：

```plaintext
property abcd; 
@(posedge clk) a |-> not (b ##1 c ##1 d); 
endproperty
```

### 如果属性（If Property）

```plaintext
if (expression) property_expr1 [ else property_expr2] 
```
如果表达式为真，则 property_expr1 必须成立；如果表达式为假，则 property_expr2 必须成立（如果存在）。示例：

```plaintext
property P2; 
@ (negedge clk) if (a) b |=> c; else d |=> e; 
endproperty
```

## 序列操作符（Sequence Operators）

### 与序列（And Sequence）

```plaintext
sequence_expr1 and sequence_expr2 
```
两个序列必须都发生，但操作数的结束时间可以不同。示例：

```plaintext
(a ##2 b) and (c ##2 d ##2 e) ;
```

### 首次匹配（First Match）

```plaintext
first_match (sequence_expr[, seq_match_item])
```
一旦找到第一次匹配，就停止对一个或多个序列的评估。示例：

```plaintext
sequence s1; 
first_match(a ##1 b[->1]:N] ## c); 
endsequence
```

### 相交序列（Intersect Sequence）

```plaintext
sequence_expr1 intersect sequence_expr2 
```
两个序列必须都发生，且序列表达式的起始和结束时间必须相同。示例：

```plaintext
(a ##2 b) intersect (c ##2 d ##2 e)
```

### 或序列（Or Sequence）

```plaintext
sequence_expr1 or sequence_expr2 
```
至少有一个序列必须发生。示例：

```plaintext
(b ##1 c) or (d[*1:2] ##1 e) or f[*2]
```

### 始终（Throughout）

```plaintext
boolean_expr throughout sequence_expr 
```
条件必须在整个序列的持续时间内成立。示例：

```plaintext
(a ##2 b) throughout read_sequence
```

### 在...内（Within）

```plaintext
sequence_expr1 within

 sequence_expr2 
```
sequence_expr1 必须在 sequence_expr2 的时间范围内匹配某一时刻。示例：

```plaintext
(a ##2 b ##3 c) within write_enable
```

## 序列方法（Sequence Methods）

```plaintext
sequence_instance.[ ended|matched|triggered]
```
标识序列的终点。示例：

```plaintext
wait (AB.triggered) || BC.triggered); 
if (AB.triggered) $display("AB triggered");
```

## 周期延迟（Cycle Delays）

```plaintext
##integral_number ##Identifier ##(constant_expression) ##[const_expr : const_expr] ##[const_expr : $]
```
指定从当前时钟周期到下一个指定行为发生的时钟周期数。示例：

```plaintext
property property P5 (AA); 
@(negedge clk) (b ##1 c) |=> (AA ##[1:2] (d||AA)); 
endproperty
```

## 序列和属性中的局部变量（Local Variables in Sequences and Properties）

```plaintext
(seq_expression {, seq_match_item}) [ repetition_op ] 
```
当 seq_expression 匹配时，执行 seq_match_item。匹配项可以是子程序调用。示例：

```plaintext
sequence data_check; 
int x; 
a ##1 (!a, x=data_in) ##1 !b[*0:$] ##1 b && (data_out=x); 
endsequence
```

## 重复（Repetition）

### 连续重复（Consecutive Repetition）

```plaintext
[* const_or_range_expression ]
```
连续重复。示例：

```plaintext
(a[*2] ##2 b[*2]) |=> (d)
```

### 跳转重复（Goto Repetition）

```plaintext
[-> const_or_range_expression ]
```
跳转重复。示例：

```plaintext
a ##1 b[->5] ##1 c
```

### 非连续重复（Non-Consecutive Repetition）

```plaintext
[= const_or_range_expression ]
```
非连续重复。示例：

```plaintext
s1 |=> (b [=5] ##1 c)
```

## 快捷方式（Shortcuts）

- R[*] 等同于 R[*0:$]
- ##[*] 等同于 ##[0:$]
- R[+] 等同于 R[*1:$]
- ##[+] 等同于 ##[1:S]

## 断言严重性任务（Assertion Severity Tasks）

### Fatal

```plaintext
$fatal ([ 0 | 1 | 2 , ] message [ , args ] ) ;
```
致命消息任务；消息可以是字符串或表达式。您可以从断言的操作块调用此任务。示例：

```plaintext
$fatal (0);
```

### 错误、警告、信息（Error, Warning, Info）

```plaintext
$error (message [ , args ] ) ; 
$warning (message [ , args ] ) ; 
$info (message [ , args ] ) ;
```
非致命消息任务；消息可以是字符串或表达式。您可以从断言的操作块调用这些任务。示例：

```plaintext
$error("Unsupported memory task command %b", m_task); 
$warning("Enable is set during non-read op: state=>%b", state);
```

## 系统函数（System Functions）

### One Hot

```plaintext
$onehot (bit_vector)
```
如果表达式中只有一个位为高电平，则返回真。示例：

```plaintext
property p1(Arg) 
@(posedge clk) $onehot(Arg); 
endproperty
```

### One Hot 0

```plaintext
$onehot0 (bit_vector)
```
如果表达式中至多只有一个位为高电平，则返回真。示例：

```plaintext
property p2(Arg) 
@(posedge clk) $onehot0(Arg); 
endproperty
```

### Is Unknown

```plaintext
$isunknown (bit_vector)
```
如果表达式中任何一位为 X 或 Z，则返回真。示例：

```plaintext
property p3(Arg) 
@(posedge clk) $isunknown(Arg); 
endproperty
```

### Count Ones

```plaintext
$countones (bit_vector)
```
返回向量中值为 1 的位数。示例：

```plaintext
property p4(Arg) 
@(posedge clk) $countones(Arg) == 4; 
endproperty
```

## 采样值函数（Sampled-Value Functions）

### 采样（Sampled）

```plaintext
$sampled(expression)
```
返回表达式在当前时钟周期的采样值。示例：

```plaintext
property propA 
@(posedge clk) (a ##1 b); 
endproperty 
p1: assert (propA) 
$display("%m passed"); 
else $warning("a == %s; b == %s", $sampled(test.inst.a), $sampled(test.inst.b));
```

### 上升沿（Rose）

```plaintext
$rose(expression)
```
如果表达式的采样值在当前时钟周期改变为 1，则返回真。示例：

```plaintext
Example: (a ##1 b) |-> $rose(test.inst.sig4);
```

### 下降沿（Fell）

```plaintext
$fell(expression)
```
如果表达式的采样值在当前时钟周期改变为 0，则返回真。示例：

```plaintext
(a ##1 b) |-> $fell(test.inst.c);
```

### 稳定（Stable）

```plaintext
$stable(expression)
```
如果表达式的采样值在当前时钟周期内保持不变，则返回真。示例：

```plaintext
(a ##1 b) |-> $stable(test.inst.c);
```

### 上次（Past）

```plaintext
$past(expression [ , n_cycles] )
```
返回表达式在上一个时钟周期或指定时钟周期数之前的采样值。示例：

```plaintext
(a == $past(test.inst.c, 5)
```

## 断言控制系统任务（Assertion-Control System Tasks）

```plaintext
$assertoff [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$asserton [ ( levels [ , list_of_mods_or_assns ] ) ] ; 
$assertkill [ ( levels [ , list_of_mods_or_assns ] ) ] ;
```
控制仿真过程中的断言检查。示例：

```plaintext
$assertoff (0, top.mod1, top.mod2.net1);
```