---
weight: 3
title: "SVA 快速入门教程"
description: "SystemVerilog Assertion（SVA） 快速入门教程；SVA Quick Tutorial"
---

## 1. 引言

- 断言主要用于验证设计的行为
- 用于监控设计实现是否符合规范的验证代码
- 指示验证工具尝试使用形式化方法证明/假设/计算给定的属性
- 更正式地捕捉设计意图，并更早地发现规范错误
- 更快地找到更多的错误及其来源
- 鼓励测量功能覆盖率和断言覆盖率
- 在整个生命周期中重复使用检查，增强回归测试

## 2. 断言的好处

### 2.1 提高设计的可观察性

- 使用断言可以在设计的任何地方创建无限数量的观察点
- 支持内部状态、数据路径和错误前置条件的覆盖分析

### 2.2 改进设计调试

- 断言有助于捕获问题源头处或附近的 DUT 的不正确功能，从而减少调试时间
- 断言失败时，可以通过只考虑与特定断言相关的依赖信号或辅助代码来进行调试
- 断言还有助于捕获不会传播到输出的错误

### 2.3 改进设计文档

- 断言捕获设计的规范。规范以断言、假设、约束、限制的形式转换为可执行形式。在整个开发和验证过程中检查规范
- 断言中的假设捕获设计假设，并不断验证假设在整个模拟过程中是否成立
- 断言始终以简洁的形式捕获规范，不会产生歧义，即断言是需求的可测试形式
- 断言与设计相辅相成，也可以在 SOC 级别启用

### 2.4 断言可用于提供功能覆盖率

- 功能覆盖率由覆盖属性（cover property）提供
- 覆盖属性用于监控功能覆盖的属性评估。它涵盖我们指定的属性/序列。
- 我们可以按照规范监控特定验证节点是否被执行。
- 可以为以下内容编写断言：
    - 模块内部的低级功能覆盖
    - 接口级的高级功能覆盖

### 2.5 可以在形式化（Formal）分析中使用这些断言
    - 形式化分析使用复杂的算法来证明或反驳设计是否在所有可能的工作状态下按预期行为运行。一个限制是，它仅在模块级别有效，而在整个芯片或SOC级别无效
    - 所需行为不是在传统测试平台中表达的，而是作为一组断言来表达。形式化分析不需要测试向量
    - 通过形式化分析，许多错误可以在设计过程中迅速且轻松地被发现，无需开发大量的测试向量

## 3. SVA 可以在哪里使用？

c
## 4. 谁编写断言？

- 白盒验证
    - 由设计工程师插入
    - 模块接口
    - 内部信号
- 黑盒验证
  - 由以下人员插入：
    - IP 提供商
    - 验证工程师
  - 外部接口
  - 端到端属性

## 5. SystemVerilog 断言示例

对复杂行为的简洁描述：在 req 信号有效后，ack 信号必须在 1 到 3 个时钟周期后到达。

![sva_example](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/sva_example.png)

## 6. SVA 的类型

- 即时断言（Immediate Assertions）
- 并发断言（Concurrent Assertions）

## 7. 即时断言

- 即时断言 = 给仿真器的指令。
- 遵循仿真事件语义。
- 作为过程语句出现，像过程块中的语句一样执行。
- 语法：`assert (expression) pass_statement [else fail_statement]`。
- 该语句是非时序性的，作为 `if` 语句中的条件处理。
- `else` 块是可选的，但它允许注册断言失败的严重性。
- 严重性系统任务：
   - `$fatal`：运行时致命错误，终止仿真。
   - `$error`：运行时错误（默认）。
   - `$warning`：运行时警告，可以通过命令行选项抑制。
   - `$info`：失败不携带特定严重性，可以抑制。
- 所有严重性系统任务都会打印严重性级别、文件名和行号、层次名称或作用域、仿真时间等信息。
- 示例：
```systemverilog
always @ (posedge clk) begin:checkResults
    assert ( output == expected ) okCount++;
    else begin
        $error("Output is incorrect");
        errCount++;
    end
end
```

## 8. 并发断言

- 并发断言 = 对验证工具的指令。
- 基于时钟语义，在时钟边缘进行评估。
- 评估中使用的变量值是采样值。
- 检测一段时间内的行为。
- 可以指定时间上的行为，因此这些被称为时间表达式。
- 断言出现在过程块和模块中。
- 示例：

```systemverilog
assert property (
    @(posedge clk) a ##1 b |-> d ##1 e
);
```
### 8.1 并发断言的层次

- 构建序列
- 评估序列
- 为序列定义通过或失败的属性
- 属性与特定块关联（例如：非法序列、测量覆盖率等）

#### 8.1.1 布尔表达式层

- 并发断言的基本层次
- 评估布尔表达式为 TRUE 或 FALSE
- 发生在并发属性的以下部分
- 在用于构建属性的序列中
- 在顶层的 `disable iff` 子句中

```systemverilog
assert property ( @(posedge clk) disable iff (a && $rose(b, posedge clk)) trigger |=> test_expr; )
```

- 对变量类型的限制：`shortreal`、`real` 和 `realtime`
    - 字符串
    - 事件
    - `chandle`
    - 类
    - 关联数组
    - 动态数组
- 表达式中的函数应为自动（`automatic`）
- 表达式中的变量必须是静态设计变量
- 在并发断言中采样变量

![concurrent_assertion](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/concurrent_assertion.png)

- 信号 `req` 在时钟 1 时值为低。在时钟 2 时，值被采样为高并保持高直到时钟 4。时钟 4 时采样的值 `req` 为低并保持低直到时钟 6。
- 注意，在时钟 5 时，仿真值变为高。但采样值仍为低。

#### 8.1.2 序列层

在布尔表达式层的基础上构建，并描述由一系列事件和其他序列组成的序列

- 线性序列：已知绝对时间关系
- 非线性序列
  - 多个事件触发序列，不依赖于时间
  - 多个序列相互作用并控制彼此
- 序列块
  - 定义一个或多个序列
  - 语法：
  
```systemverilog
sequence identifier (formal_argument_list);
    variable declarations
    sequence_spec
endsequence
```

  - 示例：
  
```systemverilog
sequence seq1 
    ~reset##5 req; 
endsequence 
```

```systemverilog
sequence seq2 
    req##2 ack;
endsequence
```

```systemverilog
sequence seq3
    seq1##2 ack
endsequence
```

- 使用：序列可以在以下块中实例化：
  - 模块
  - 接口块
  - 程序块
  - 时钟块
  - 包
  - 编译单元作用域
- `##` 延迟操作符：用于连接由事件组成的表达式。
    - 用法：
    - `## integral_number`
    - 标识符
    - `## (constant_expression)`
    - `## [cycle_delay_const_range_expression]`
    - 操作符 `##` 可以在同一链中使用多次。例如，`a ##1 b ##2 c ##3 d`
    - 你可以使用 `##` 和 `1'b1` 无限制地增加事件链的长度。下面的例子将前面的事件链延长了 50 个时钟周期。例如，`a ##1 b ##2 c ##3 d ##50 1'b1`
    - 序列重叠表示 `b` 在 `a` 结束时刻的同一时钟周期开始：`a ##0 b`
    - 序列连接表示 `b` 在 `a` 结束后一时钟周期开始：`a ##1 b`
    - 你可以使用整数变量代替延迟。例如，`a ##delay b`
    - 以下表示 `b` 在 `a` 完成后 2 个时钟周期内完成（无论 `b` 何时开始）：`a ##2 b.ended`
    - 你还可以指定绝对延迟的范围。例如，`a ##[1:4] b`。你也可以使用变量延迟范围。例如，`a ##[delay1:delay2] b`
    - 延迟范围中的符号 `$` 表示信号或事件将“最终”发生。例如，`a ##[delay1:$] b`
- 序列与时钟
  - 隐式时钟：
  
```systemverilog
sequence seq1
    ~reset##5 req;
endsequence
```

  - 在序列中使用时钟：
  
```systemverilog
sequence Sequence3;
    @(posedge clk_1) // 时钟名称为 clk_1
    s1 ##2 s2; // 两个序列
endsequence
```

- 序列操作

![sequence_oper](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/3/sequence_oper.png)

  - 重复操作符
    - 有三种类型的重复操作符。
      - 连续重复操作符 [* ]
      - 非连续重复操作符 [= ]
      - 跳转重复操作符 [-> ]
  
- 连续重复操作符
  + 表示序列按指定次数重复。例如，`s1 ##2 s2 [*4] ##5 s3` 与 `s1 ##2 (s2 ##1 s2 ##1 s2 ##1 s2) ##5 s3` 等效，或者简化为 `s1 ##2 s2 ##1 s2 ##1 s2 ##1 s2 ##5 s3`
  + 空序列 [*0]：重复 0 次表示结果为空
    - 用法规则：
      + `(e ##0 s)` 或 `(s ##0 e)` 不匹配任何序列。
      + `(e ##n s)` 等价于 `(##(n-1) s)`，如果 n > 0
      + `(s ##n e)` 等价于 `(s ##(n-1) true)`，如果 n > 0
  + 范围重复
    - 可以使用范围指定重复操作符。例如，`s1 [*2:3]` 等价于 `s1 ##1 s1`（两次 `s1`）或 `s1 ##1 s1 ##1 s1`（三次 `s1`）
    - 范围重复也适用于事件链。例如，`(s1 ##5 s2) [*2:3]` 等价于 `(s1 ##5 s2) ##1 (s1 ##5 s2)`（两次 `(s1 ##5 s2)`）或 `(s1 ##5 s2) ##1 (s1 ##5 s2) ##1 (s1 ##5 s2)`（三次 `(s1 ##5 s2)`）
    - 范围中的上限 `$` 表示序列表示指定的下限。例如，`s1[*2:$]`、`s0 ##3 s1[*2:$] ##2 s2`
  
- 非连续精确重复操作符
  + 表示布尔表达式超过操作数的最后一个 `true` 值。
  + `b [=3]`：布尔表达式 `b` 在三次时钟周期内为真，但不一定是连续的，且可能在最后一次 `true` 后有额外的时钟周期。
  + `b [=3:5]`：布尔表达式 `b` 为真 3、4 或 5 次，同样不一定在连续的时钟周期内，并且在 `b` 为 `false` 时可能有额外的时钟周期。
  + `a ##2 b [=3] ##4 c`：布尔表达式 `b` 为真三次，但不一定在连续时钟周期内。第一次 `b` 发生在 `a` 之后两个时钟周期。最后一次发生在 `c` 之前四个时钟周期。
  
- 跳转重复操作符
  + 布尔表达式的跳转重复操作符，在表达式为 `true` 时结束。
  + `b [->3]`：布尔表达式 `b` 为真三次，但不一定在连续时钟周期内。
  + `b [->3:5]`：布尔表达式 `b` 为真 3、4 或 5 次，且不一定在连续时钟周期内。
  + `a ##2 b [->3] ##4 c`：布尔表达式 `b` 为真三次，但不一定在连续时钟周期内。第一次 `b` 发生在 `a` 之后两个时钟周期。最后一次发生在 `c` 之前四个时钟周期。

- 值变化函数：SVA 采样值函数检测信号/表达式上的事件，并可在断言中使用

| 函数 | 含义 |
| --- | --- |
| `$rose (expression)` | 如果表达式的最低有效位变为 1，则返回 `true`，否则返回 `false` |
| `$fell (expression)` | 如果表达式的最低有效位变为

 0，则返回 `true`，否则返回 `false` |
| `$stable (expression)` | 如果表达式的值没有变化，则返回 `true`，否则返回 `false` |
| `$past (expression)` | 如果表达式在上一个时钟周期时为真，则返回 `true`，否则返回 `false` |
| `$changed (expression)` | 如果表达式的值在当前时钟周期内发生了变化，则返回 `true`，否则返回 `false` |

### 8.1.3 属性层

- 基于序列、布尔表达式构建
- 属性块（`property`）声明语法：
  
```systemverilog
property identifier (formal_arg_list);
  variable_declarations
  property_spec
endproperty
```

- 属性声明可以出现在以下位置：
  - 模块（module）
  - 接口（interface）
  - 程序（program）
  - 时钟块（clocking block）
  - 包（package）
  - 编译单元（compilation unit）
  
- 属性声明在仿真中不会生效，直到被明确指定为：
  - 假定或预期行为：通过 `assume` 关键字关联属性，验证环境假定该行为发生。
  - 检查器：通过 `assert` 关键字关联属性，验证环境检查行为是否发生。
  - 覆盖规范：通过 `cover` 关键字关联属性，验证环境用于测量覆盖率。

#### 属性类型

- **属性类型 1**：序列（Sequence）
  - 属性表达式可以是简单的序列表达式，如下所示：
  
```systemverilog
property sequence_example;
  s1; // s1 是定义的序列
endproperty
```
  - 如果序列不是空匹配，则该属性是有效的。

- **属性类型 2**：另一个属性
  - 可以使用命名属性的实例作为有效的属性表达式。例如，上面定义的 `sequence_example` 就可以作为属性表达式：
  
```systemverilog
property property_example;
  Sequence_example
endproperty
```

- **属性类型 3**：属性的逆（Inverse）
  - 属性表达式可以是另一个属性的逆。逆操作通过 `not` 运算符实现：
  
```systemverilog
property inversion_example;
  not Sequence_example
endproperty
```

- **属性类型 4**：属性的析取（Disjunction）
  - 析取属性如果其组成属性表达式之一为真，则为真。使用 `or` 运算符描述析取：
  
```systemverilog
property disjunction_example;
  sequence_example or inversion_example;
endproperty
```

- **属性类型 5**：属性的合取（Conjunction）
  - 合取属性等价于逻辑与操作，使用 `and` 运算符描述：
  
```systemverilog    
property conjunction_example;
  sequence_example and inversion_example
endproperty
```

- **属性类型 6**：`if..else` 语句
  - 条件属性表达式，描述基于表达式值的两种行为：
  
```systemverilog
property ifelse_example;
  if ( expr == 2’b10)
    inversion_example;
  else sequence_example
endproperty
```

- **属性类型 7**：蕴涵（Implication）
  - 蕴涵属性描述在前置行为发生时，后续行为将会发生。使用运算符 `|->` 和 `|=>` 描述：
  
```systemverilog
property implication_example;
  s0 |-> sequence_example
endproperty
```

#### 蕴涵构造

- 有两种类型：
  - `->`
  - `=>`

- 用法：
  - `Res = A (前提) -> B (结论)`
  - 说明：
    - 如果前提（`A`）与结论（`B`）不匹配，则该蕴涵成功且为真。
    - 如果前提不匹配，蕴涵成功并返回真（被称为空合成功）。

- 真值表：

| A  | B  | Res |
|----|----|-----|
| 0  | 0  | Vacuous success |
| 0  | 1  | Vacuous success |
| 1  | 0  | False |
| 1  | 1  | True |

- 示例：

```systemverilog
property data_end;
  @(posedge mclk)
   Data_phase |->  ((irdy==0) && ($fell(trdy) || $fell(stop)));
endproperty
```

- 运算符优先级和关联性表：

| 序列操作符 | 属性操作符 | 属性关联性 |
|------------|------------|------------|
| [*], [=], [->]  |  | - |
| ##         |  | 左侧 |
| throughout |  | 右侧 |
| within     |  | 左侧 |
| intersect  |  | 左侧 |
|            | not        |  |
| and        | and        | 左侧 |
| or         | or         | 左侧 |
|            | if..else   | 右侧 |
|            | |->, |=>   | 右侧 |

#### 使用序列的并发断言

```systemverilog
sequence s1;
   @(posedge clk) a ##1 b ##[1:2] c;
endsequence;
My_Assertion : assert property (@(posedge clk) s1);
```

#### 使用属性的并发断言

```systemverilog
property p1;
  @(posedge clk) s1 ##1 s1 ##1 s1;
endproperty
Top_Assertion : assert property (p1) pass_stmt;
else fail_stmt;
```

- 还可以使用 `cover` 构造，进行功能覆盖率测量：
  
```systemverilog
cover property (p1);
```

#### 属性表达式限定符

- **时钟事件（Clocking event）**
  - 时钟事件描述属性表达式应何时生效。如下示例：

```systemverilog
property clocking_example;
@(posedge clk) Sequence_example
endproperty
```

- **禁用条件（Disable iff）**
  - `disable iff` 命令类似于复位语句，属性表达式仅在复位条件解除后生效。示例如下：

```systemverilog
property disable_iff_example;
  Disable iff (reset_expr) Sequence_example
endproperty
```

#### 递归属性

- 示例：

```systemverilog
property recursive_always;
  Sig_x and (1’b1 |=> recursive_always);
endproperty
```

- 递归属性的限制：
  - 递归属性不能使用 `not` 运算符。
  - 递归属性中不能使用 `disable iff` 运算符。
  - 递归属性只能在正时延迟后调用自己（以避免无限循环）。

#### 断言层

- 断言层为属性提供语义，使属性具备行为判断。
- 关键字：
  - `assert`：指示属性作为检查器，验证环境应检查该行为是否发生。
  - `assume`：指示属性行为是预期的，验证工具应按此处理。
  - `cover`：如果属性关联了 `cover`，则表示该属性评估将被用于覆盖率监控。

- 并发断言可以在以下构造内定义：
  - `always` 块
  - `initial` 块
  - 模块
  - 程序
  - 接口
  
- 当属性实例化在过程块外（如 `initial` 或 `always`）时，属性的行为类似于在 `always` 块中：

```systemverilog
always
assert property (p1);
```
### 8.2 assert 语句

- 与 `assert` 语句关联的属性被视为检查器（checker），用于验证行为。

```systemverilog
property top_prop;
  seq0 |-> prop0;
endproperty

assert to_prop:
  assert property (top_prop) begin
    int pass_count;
    $display ("pass: top_prop");
    pass_count = pass_count + 1'b1;
  end
```

### 8.3 assume 语句

- 与 `assume` 语句关联的属性表示在验证过程中该属性应成立。
- 对于形式化验证或动态仿真环境，该语句的属性简单地假定为真，并且其他需要验证的语句会相应地进行约束。

```systemverilog
Assume_property_reset_seq0: assume property (reset_seq0);
property reset_seq0;
  @(posedge clk) reset |-> not seq0;
endproperty
```

### 8.4 cover 语句

- `cover` 语句用于测量各个组件的覆盖率。

```systemverilog
cover_property_top_prop:
  cover property (top_prop);
  $display ("top_prop is a hit");

property top_prop;
  seq0 |-> prop0;
endproperty
```

### 8.5 expect 语句

- `expect` 语句与 `assert` 语句非常相似，但必须出现在过程块（包括 `initial` 或 `always` 块、任务和函数）中，并且用于在属性成功之前阻止执行。

```systemverilog
task mytask;
  ...
  if (expr1)
    expect (my_property)
    pass_block();
  else // 与 'expect' 相关联，
       // 而不是与 'if' 相关联
    fail_block();
  ...
endtask
```

---

## 9. 属性绑定到作用域或实例

- 为了方便验证而不修改设计代码，可以将属性绑定到特定的模块或实例。
- 使用：
  - 允许验证工程师在不修改设计代码/文件的情况下进行验证。
  - 提供了一个方便的机制，将 VIP（验证 IP）附加到模块或实例。
  - 由于此功能，断言不会产生语义上的变化。它等同于使用层次路径名称编写外部属性。

### 绑定两个模块的示例

```systemverilog
module cpu (a, b, c);
  < RTL 代码 >
endmodule

module cpu_props (a, b, c);
  < 断言属性 >
endmodule
```

- 使用 `bind` 关键字将属性绑定到模块实例：

```systemverilog
bind cpu cpu_props cpu_rules_1(a, b, c);
```

- `cpu` 和 `cpu_props` 是模块名称。
- `cpu_rules_1` 是 `cpu_props` 实例的名称。
- 端口（`a`，`b`，`c`）绑定到模块 `cpu` 的信号（`a`，`b`，`c`）。
- 每个 `cpu` 实例都将获取这些属性。