---
weight: 4
title: "Safety 属性和 Liveness 属性"
description: "Safety 属性和 Liveness 属性；Safety Properties and Liveness Properties"
---

## 1. 安全性属性（Safety Properties）

安全性属性检查的是坏事永远不会发生。它是FPV中最常用的属性类型，因为与活性属性相比，求解器找到证明要简单得多。

安全性属性可能产生以下结果：

- 得到完整证明，意味着求解器可以保证“坏事”永远不会发生。
- 得到有界证明，表明“坏事”在某些周期内无法发生。
- 一个有限前缀的反例，显示“坏事”发生的路径。

下面是从IHI0051A amba4 axi4流提取的一个安全性属性示例：

```systemverilog 
   /* ,         ,                                                     *
    * |\\\\ ////| "Once TVALID is asserted it must remain asserted    *
    * | \\\V/// |  until the handshake (TVALID) occurs".              *
    * |  |~~~|  |  Ref: 2.2.1. Handshake Protocol, p2-3. 	      *
    * |  |===|  |						      *
    * |  |A  |  |						      *
    * |  | X |  |						      *
    *  \ |  I| /						      *
    *   \|===|/							      *
    *    '---'							      */
   property tvalid_tready_handshake;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && !TREADY |-> ##1 TVALID;
   endproperty // tvalid_tready_handshake
```
            安全属性表示如果接收方无法处理数据包，则不应丢弃该数据包。

## 2. 活性属性（Liveness Properties）

活性属性检查的是某件好事最终一定会发生。如

- 解码算法最终会终止。
- 每个请求最终都会得到确认。

这类属性在FPV中检查起来更复杂，因为与安全性属性不同，活性属性的 CEX 不能在单一状态下找到。为了找到CEX，必须提供足够的证据，证明“好事”可能永远被推迟，有时还需要辅助属性来帮助求解器理解有某种进展正在发生（公平性假设）。

安全性属性可以通过什么都不做来证明，因为这永远不会导致“坏事”的发生。活性属性与安全性属性相辅相成，但它们更难证明，因为求解器需要保证某件事会无限多次发生。

下面是一个活性属性的示例，来自经典仲裁器问题，表明每个请求必须最终得到授权，可以通过SVA如下描述：

```systemverilog 
property liveness_obligation_arbiter;
  req |=> s_eventually gnt
endproperty
```

另一个活性属性的示例，定义了发送方和接收方之间必须最终发生握手，来自IHI0022E AMBA和AXI协议规范，如下所示：
```systemverilog 
   // Deadlock (ARM Recommended)
   /* ,         ,                                                     *
    * |\\\\ ////|  It is recommended that READY is asserted within    *
    * | \\\V/// |  MAXWAITS cycles of VALID being asserted.           *
    * |  |~~~|  |  This is a *potential deadlock check* that can be   *
    * |  |===|  |  implemented as well using the strong eventually    *
    * |  |A  |  |  operator (if the required bound is too large to be *
    * |  | X |  |  formally efficient). Otherwise this bounded        *
    *  \ |  I| /   property works fine.                               *
    *   \|===|/                                                       *
    *    '---'                                                        */
   property handshake_max_wait(valid, ready);
      valid & !ready |-> strong(##[1:$]) ready;
   endproperty // handshake_max_wait
```
            使用活性属性检查死锁条件。这是一种非常常见的做法。

一个 liveness 解决方案的简单示例：

![liveness_reso](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness_reso.png)

### 2.1 liveness 示例

liveness 特性对于 FPV 非常重要，尤其是对于验证设计没有死锁、活锁、饥饿和信息丢失。其中一个 liveness 问题，除了难以实现证明收敛之外，是调试它们：理解 safety CEX 有时可能很困难，但解释 liveness 的 CEX 可以是一门艺术。

下面是一个简单的有限状态机

![live_fsm](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/live_fsm.webp)

此 FSM 代码如下： 

```systemverilog 
`default_nettype none
module liveness
  (input bit clk, rstn,
   input bit  start,
   output bit done);

   typedef enum logic [1:0] {idle, decrypt, validate_key, inform_result} states_t;
   states_t ps;

   default clocking fpv_clk @(posedge clk); endclocking

   // Drive the reset sequence
   init0: assume property($fell(rstn) |=> ps == idle);
   init1: assume property($rose(rstn) |=> rstn);

   // Drive outputs
   ap_done: assume property(ps == inform_result |=> done);
   
   // Write the state machine transitions as assumptions
   state0: assume property(disable iff(!rstn)
			   start && ps == idle |=> ps == decrypt);
   
   state1: assume property(disable iff(!rstn)
			   ps == decrypt |=> ps == validate_key);
   state2: assume property(disable iff(!rstn)
			   ps == validate_key |=> ps == inform_result);
   state3: assume property(disable iff(!rstn)
			   ps == inform_result |=> ps == idle);
   
   // A weak unbounded property that cant catch the deadlock
   ap_deadlock: assert property(disable iff(!rstn)
				ps == idle |-> ##[1:$] ps == inform_result);

   // A liveness property to check for FSM deadlocks better than ap_deadlock
   ap_deadlock_2: assert property(disable iff(!rstn)
				  ps == idle |=> s_eventually ps == inform_result);
endmodule // liveness
```

该属性 ap_deadlock 被写入以捕获任何死锁，但由于无界延迟运算符的弱特性，这将无法实现（但为什么？）。属性 ap_deadlock_2 是解决这个问题的更好方案。通过运行 `sby -f ./src/liveness/liveness.sby err` 可以看到，尽管 FSM 序列是正确的，但 SBY 显示属性失败，而且没有 VCD 文件用于调试。现在该怎么办？

调试活跃性属性的一种技术是通过使用有界安全断言来判断活跃性义务是否得以履行。如果此类属性失败，则意味着缺少一个公平性假设。在这种情况下，活跃性义务是 `ps == inform_result`。读者可以分析图 5.12 来理解发生了什么（提示：有两条返回到空闲状态的路径，一条当 `start` 为 0 时，另一条当 `start` 可以变为 1 时，只有其中一条路径满足活跃性义务）。

如前所述，未来的应用笔记将深入讨论这一点，但为了继续这个例子，缺失的公平性假设的解决方案如下： 
```systemverilog
   ap_fairness: assume property(disable iff(!rstn)
   				!start |=> s_eventually start);
```
取消注释第 45 到 48 行以启用 ap_fairness 假设。

通过在第 32 行填写一个错误的状态并运行 `sby -f ./src/liveness/liveness.sby pass`，死锁将被属性捕获，现如今我们知道 CEX 是正确的，而不是一个虚假的假阴性。

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

