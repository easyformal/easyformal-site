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
   //一旦 TVALID 被断言，它必须保持断言状态直到握手 (TVALID) 发生
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

这类属性在FPV中检查起来更复杂，因为与安全性属性不同，活性属性的 CEX（反例） 不能在单一状态下找到。为了找到 CEX，必须提供足够的证据，证明“好事”可能永远被推迟，有时还需要辅助属性来帮助求解器理解有某种进展正在发生（公平性假设）。

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
   // 建议在 VALID 被断言的 MAXWAITS 周期内断言 READY。这是一个潜在死锁检查，也可以使用强 eventually 运算符来实现（如果所需的界限太大而无法正式有效）。否则，这个有界属性可以正常工作。
   property handshake_max_wait(valid, ready);
      valid & !ready |-> strong(##[1:$]) ready;
   endproperty // handshake_max_wait
```
            使用活性属性检查死锁条件。这是一种非常常见的做法。

一个 liveness 解决方案的简单示例：

![liveness_reso](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness_reso.png)

### 2.1 liveness 示例

活性属性对于FPV非常重要，尤其是在证明设计没有死锁、活锁、饥饿和信息丢失时。活性问题的一个挑战，除了证明收敛的难度外，还有调试活性问题：理解安全性反例（CEX）有时会很困难，但解释活性反例（CEX）则是一门艺术。

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
解释：这段代码展示了一个简单的Verilog模块，用于验证活性属性。模块有几个输入（clk, rstn, start）和输出（done）。状态机有四个状态：idle, decrypt, validate_key, inform_result。每个状态之间的转移都被写成假设（assume）属性，表示在特定条件下状态的转移。

- init0 和 init1 定义了复位序列。
- ap_done 属性表示当状态机进入 inform_result 状态时，done 输出应该被置为真。
- state0 到 state3 定义了不同状态之间的转移规则。
- ap_deadlock 是一个弱的、无界的属性，试图捕捉死锁，但由于延迟操作符的弱性，无法真正捕捉死锁。
- ap_deadlock_2 是一个改进的活性属性，检查是否存在死锁。

ap_deadlock 这个属性尝试捕捉死锁，但由于使用了无界延迟操作符（##[1:$]），它不能有效地捕捉死锁。该属性没有限定最大延迟范围，导致它无法对系统状态的长期行为做出有效检查。ap_deadlock_2 属性通过使用 s_eventually 来改进活性检查，能够更准确地捕捉死锁。

为了调试活性属性，可以通过添加有界安全性断言来检查是否满足活性义务。如果该断言失败，就表明系统中可能缺少某些公平性假设。例如，在这个例子中，活性义务是确保系统最终能够进入 inform_result 状态。由于有两个返回到 idle 的路径，只有在特定条件下（例如 start 变为 1）才满足活性义务。

缺失的公平性假设的解决方案如下：

```systemverilog
   ap_fairness: assume property(disable iff(!rstn)
   				!start |=> s_eventually start);
```
此时填写一个错误的状态并运行FPV，死锁将被该属性捕获，此时我们知道 CEX 是正确的，而不是一个虚假的假阴性。

```systemverilog
   ps == validate_key |=> ps == <state>); // correct state
```

### 2.2 有界活性（Bounded Liveness）

![有界活性示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/bounded_liveness.png)

**断言**：属性 P 必须在起始触发事件发生之后以及结束触发事件发生之前有效。

**补充解释**：
- **时间限制**：通过明确的起始和结束事件来限制属性的验证范围，使问题更易于处理。

### 2.3 不变量（Invariants）

![不变量示意图](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/invariant.png)

**不变量断言窗口**：属性 P 在起始事件发生后必须保持有效，并且在结束事件发生前持续接受检查。

**补充解释**：
- **始终有效**：不变量属性通常用于关键部分，确保其在整个运行期间没有被破坏，例如系统状态或数据一致性。

