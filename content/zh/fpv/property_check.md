---
weight: 0
title: "使用 SystemVerilog 断言进行属性检查 "
description: "使用 SystemVerilog 断言进行属性检查 "
draft: true

---

<!-- 



### 1. 断言类型

#### 1.1 立即断言

立即断言是纯粹的组合元素，不允许时间域事件或序列。立即断言具有以下属性：

- 非时间性的
    + 它们会同时被评估和报告（它们不能等待任何临时时间）
- 立即进行评估
    + 在断言条件变量激活时对其取值进行采样。
- 更简单的计算语义
    + 时钟同步的立即断言不具有并发断言的语义
- 只能在程序块中指定

下图为立即断言示例，包含有时钟和无时钟语义：

![immediate0](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/fpv/image/0/immediate0.png)

#### 1.2 并发断言

并发断言捕捉跨越时间的事件序列，也就是说，它们具有时间域，在系统的每个时钟周期或时间步长时进行评估。

并发断言可以定义在：

- initial 或 always 块
- 在 SystemVerilog 的 `module` 或 `checker` 对象内部。

- 在 SystemVerilog 的 interface 内部
- 对于仿真，在 program 块里面

下图为并发断言示例，分别在过程块代码中定义和作为独立定义：

![immediate0](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/fpv/image/0/immediate0.png)

##### 1.2.1 时钟或时间步长

并发断言与时钟相关联，时钟定义了采样时钟或断言被评估的时间点。这种结构有助于明确定义采样值函数的事件，相关内容将在后续部分讨论。可以使用 default clocking 关键字定义并发属性的默认时钟事件，作为所有并发属性的主时钟。

##### 1.2.2 Disable 条件

同样，某些属性可能需要在某些事件期间禁用，因为其结果在这些情况下无效，例如在复位状态时。可以使用 default disable iff (event) 关键字来定义何时不打算检查并发断言的结果。以下是默认复位和默认时钟定义的示例。

```
// Concurrent properties are checked each *posedge* PCLK
default clocking
   formal_clock @(posedge PCLK);
endclocking

// And disabled if the *PRSTn* reset is deasserted
default disable iff (!PRSTn);

/* The property does not need to explicitly
 * define PCLK as main clock and !PRSTn as disable event, as it is
 * defined in the default clocking and disable blocks. */
property_a: assert property (RxStatus == 3'b011 |-> ##1
			     Receiver_detected);
```

默认时钟和默认禁用事件的使用情况用于表明每个 posedge PCLK 都会检查所有并发属性，并且如果 PRSTn 复位被取消，则禁用所有并发属性。

### 2. SVA 的元素

#### 2.1 SVA 元素分层

并发属性主要由四层元素组成：

- 布尔层
- 时钟或序列层
- 属性层
- 验证层

##### 2.1.1 布尔层

示例：

```
!(|(~TKEEP & TSTRB));
```

当 TKEEP 任何一位为 0 且同一位在 TSTRB 为 1 时，该布尔表达式为逻辑 1,否则结果为 0。

另一种可以在布尔层中表达的构造是布尔不变性属性。布尔不变性（或不变）属性在任何状态下评估为真，换句话说，这是一种始终成立的属性。例如：

```
ap_never: assert property (@(posedge clk) disable iff(!rstn)
                           !packet_error);
```




--> 