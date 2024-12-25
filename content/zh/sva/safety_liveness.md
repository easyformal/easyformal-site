---
weight: 4
title: "Safety 属性和 Liveness 属性"
description: "Safety 属性和 Liveness 属性；Safety Properties and Liveness Properties"
---

### 安全性属性（Safety Properties）

**安全性（Safety）**：确保不发生任何不好的事情。以下是一些例子：
- FIFO 不会溢出。
- 系统不允许多个进程同时修改共享内存。
- 请求在 5 个时钟周期内获得响应。

更正式地说，安全性属性的含义是：任何违反该属性的路径都会有一个有限的前缀，而这个前缀的每个扩展也都会违反该属性。因此，通过有限的模拟运行可以验证是否存在违反安全性属性的情况。

**补充解释**：
- **FIFO 溢出**：当数据缓冲区超过其最大容量时可能发生的问题，通过安全性属性，我们可以确保这种情况永远不会发生。
- **共享内存访问冲突**：多个进程同时访问或修改共享内存可能导致不一致性，通过安全性检查可以避免。
- **响应时间限制**：通过属性定义，确保系统的每个请求都在规定的时间内得到响应。

### 活性属性（Liveness Properties）

**活性（Liveness）**：保证最终会发生一些好事情。以下是一些例子：
- 解码算法最终会终止。
- 每个请求最终都会得到确认。

更正式地说，活性属性的含义是：任何有限的路径都可以扩展为满足该属性的路径。

![活性示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness.png)

![活性详细示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness2.png)

**断言**：属性 P 在触发事件发生后必须最终有效。

**补充解释**：
- **解码算法最终会终止**：表示系统能够确保处理流程在合理时间内完成，而不是无限循环。
- **请求确认**：即使有复杂的条件限制，每个请求最终也能被系统接受并确认。

理论上，活性属性只能通过无限次的模拟运行来验证是否会发生违反。但在实际中，我们通常通过“优雅的测试结束”（假设测试运行到某个点表示无限时间）来近似验证活性属性。

- 如果好事情未在规定的测试期限内发生，我们会假设它永远不会发生，从而视为该属性被验证为假。

#### 有界活性（Bounded Liveness）

![有界活性示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/bounded_liveness.png)

**断言**：属性 P 必须在起始触发事件发生之后以及结束触发事件发生之前有效。

**补充解释**：
- **时间限制**：通过明确的起始和结束事件来限制属性的验证范围，使问题更易于处理。

#### 不变量（Invariants）

![不变量示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/invariant.png)

**不变量断言窗口**：属性 P 在起始事件发生后必须保持有效，并且在结束事件发生前持续接受检查。

**补充解释**：
- **始终有效**：不变量属性通常用于关键部分，确保其在整个运行期间没有被破坏，例如系统状态或数据一致性。

