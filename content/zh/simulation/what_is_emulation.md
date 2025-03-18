---
weight: 1
title: "什么是 Emulation"
description: "什么是 Emulation"
draft: true
---

### 介绍：

众所周知，我们的芯片现在加载了大量功能，因此设计的规模正在快速增长。现代 SoC/ASIC 在门数以及支持的功能方面越来越大。在这种情况下，主要挑战是实现严格的上市时间，并对如此大型的 ASIC/SoC 执行令人满意的功能验证。

主要使用以下技术来实现功能验证收敛：

- RTL Simulation
- Formal or Static Verification
- FPGA Prototyping
- Emulation

在 Functional Verification Flow 中，“Emulation”越来越流行。Emulation 是指使用专业计算机（通常称为“Emulator”），它自动将设计的 RTL 表示映射到其内部可编程门阵列，以执行设计的硬件和软件的功能验证。

### 采用 Emulation 动机

1. 增加 SoC 设计的门数。现在，一个典型的 SoC 包含大约 5000 万个门。Simulators 在性能方面实际上并不那么高效，无法处理如此大的设计。

2. 上市时间压力意味着实现更高效的硬件/软件协同验证的策略变得越来越有吸引力。尽管前期成本相对较高，但 Emulation 仍提供此功能。

3. 与 FPGA 原型设计相比，Emulators 提供更短的编译时间以及更好的调试和波形可见性。

4. 当今 emulators 的系统级功能使其能够在设计项目中比以前更早地使用，以帮助在更高的抽象级别做出决策。这也有助于证明他们的成本是合理的。

5. 今天的 emulators 是经过架构设计的，既可以在云中使用（因此它们可以由地理位置分散的设计团队共享），也可以实现可扩展性（可以连接多个 emulators 以用于同一项目，以进一步缩短运行时间）。

6. 嵌入式软件验证。

让我们用一些基准数据来详细说明上面的第 1 点——

在设计为 200 MHz 的 1 亿个门电路中执行 1 秒的真实数据需要执行 2 亿个周期。即使在具有大量缓存大小和大量 RAM 的最快 CPU 上，RTL Simulator 也需要三周以上的速度，每秒 100 个周期——这是一个乐观的假设——才能完成设计。它清楚地表明，RTL Simulation 并不是大型设计在有意义的时间内执行实时数据的有效方式。如果只测试小时间框架，则可能会发现许多可能的差距和错误。

### 比较不同的验证技术：

在下面的图表中，显示了不同验证技术之间的比较，即 RTL Simulation、FPGA原型设计和现代 Emulation，以及各种参数，例如。

- 设计容量
- 性能
- 设置和编译时间
- 设计调试功能

![Comparing](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/simulation/image/1/Comparing.png)

图 1：RTL 仿真、FPGA 原型设计和硬件仿真的比较基于性能、设置/编译时间、设计能力和设计调试。（来源： Lauro Rizzatti 博士）

在下面的图 2 中，显示了不同选项支持的功能：

![Emulation_Landscape_1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/simulation/image/1/Emulation_Landscape_1.webp)

图 2：不同技术支持的功能（来源：Lauro Rizzatti 博士）


市场上的三大主要参与者——Cadence Design Systems （Palladium XP）、Mentor Graphics （Veloce） 和 Synopsys （ZeBu）——提供的高级 Emulators 都能够处理系统级（例如 C、C++、事务级模型）和 RTL 设计。

