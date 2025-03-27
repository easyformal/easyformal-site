---
weight: 1
title: "SAT 与 SMT 求解器：现代验证工具"
description: "SAT 与 SMT 求解器：现代验证工具"
draft: true
---

## 1. 引言

SAT 和 SMT 求解器是计算机科学中形式验证和自动推理领域的核心工具。SAT 问题关注于判断一个命题逻辑公式是否存在一个满足其为真的变量赋值，而 SMT 求解器则在 SAT 的基础上扩展，支持更复杂的逻辑理论（如算术、数组、函数等），从而能够处理更广泛的验证任务。

## 2. SAT 问题

### 2.1 定义

SAT 问题：给定一个命题逻辑公式 $ \alpha $，判断是否存在一个满足解（satisfying solution），即一组变量赋值使得 $ \alpha $ 为真。

- 示例：  
  $$\(\alpha(x_1, x_2, x_3) := (x_1 \wedge x_2 \vee x_3) \wedge (x_1 \wedge \neg x_3 \vee x_2)\)$$
  满足解：$$\(x_1 = 1, x_2 = 1, x_3 = 0\)$$

### 2.2 复杂性

由于需要检查所有可能的赋值组合，SAT问题的计算复杂性为 $2^n$ （其中 $n$ 为变量数），属于指数级。

SAT问题是第一个被证明为NP完全（NP-complete）的问题（Cook, 1971）。尽管其复杂性很高，经过30多年的工程努力，现代SAT求解器已能有效解决许多实际问题。

### 2.3 SAT 在验证中的应用

SAT问题在形式验证中有着广泛应用，尤其是在自动机的可达性分析和不变性检查中。以下是两个典型问题及其SAT编码：

#### 问题1：可达性分析

问题：状态$\(U\)$是否在\(n\)步内从初始状态\(Q_0\)可达？

SAT编码：
  $$ F_{Q_0}(X_0) \wedge F_T(X_0, X_1) \wedge \cdots \wedge F_T(X_{n-1}, X_n) \wedge F_U(X_n)   $$

  - $\(F_{Q_0}(X_0)\)$：表示初始状态集合的公式。
- $\(F_T(X_i, X_{i+1})\)$：表示状态转移关系的公式。
- $\(F_U(X_n)\)$：表示目标状态集合的公式。

  若公式可满足（SAT），则 $ U $ 可达；若不可满足（UNSAT），则不可达。

#### 问题2：不变性检查

问题：集合$\(I\)$是否为自动机$\(\mathcal{A}\)$的不变集（inductive invariant）？

  $$ F_{Q_0}(X) \rightarrow F_I(X) \wedge F_I(X) \wedge F_T(X, X') \rightarrow F_I(X') $$

- 若此公式为真，则$\(I\)$是不变集；否则不是。

## 3. 命题逻辑与电路表示

### 3.1 基本术语

- 变量：如 $x_1, x_2$
- 文字（Literal）：变量的正或负形式，如 $\(x_1, \neg x_2\)$
- 子句（Clause）：文字的析取，如 $\((x_1 \vee \neg x_2 \vee x_3)\)$
- 合取范式（CNF）：子句的合取，如 $\((x_1 \vee x_2 \vee \neg x_3) \wedge (\neg x_2 \vee x_1)\)$

SAT 求解器通常假设输入公式为 CNF 形式。

### 3.2 电路表示

命题逻辑公式可以通过逻辑电路表示，常见的逻辑门包括：

![circuit](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/solver/image/1/circuit.png)

- AND（与）
- NAND（与非）
- OR（或）
- NOR（或非）
- NOT（非）
- XOR（异或）
- XNOR（同或）


为了提高效率，可以通过重命名子表达式来简化公式。以下是两种等价性概念：

- 重言等价（Tautologically Equivalent）：两个公式的每个满足解相同。
- 等价可满足性（Equisatisfiable）：一个公式可满足当且仅当另一个公式可满足。

示例：  


![demo1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/solver/image/1/demo1.png)

![demo2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/solver/image/1/demo2.png)


$$
(A \wedge B) \leftrightarrow E
$$

扩展为：

$$
I' \equiv (D \wedge E) \vee (\neg C \wedge E) \wedge ((A \wedge B) \leftrightarrow E)
$$

$\(I\)$和$\(I'\)$并非重言等价，但具有等价可满足性（如赋值$\(C=0, A=1, B=1, E=0\)$满足$\(I\)$）。


对于 $\((A \wedge B) \leftrightarrow E\)$，可以将公式重写为等满足的 CNF 形式，从而简化计算。

## 4. 转换为 CNF

将命题逻辑公式转换为CNF的步骤如下：

1. 将公式视为电路：识别逻辑门的层次结构。
2. 为非叶节点命名：为每个中间表达式引入新变量。
3. 添加输入/输出子句的合取：为每个非叶节点生成等价约束。
4. 取所有内容的合取：组合所有子句。

示例：

$$
E \leftrightarrow (A \wedge B)
$$

转换为：

$$
(\neg A \vee \neg B \vee E) \wedge (\neg E \vee A) \wedge (\neg E \vee B)
$$

其他示例包括：

$$
G \leftrightarrow (D \wedge E), \quad \neg F \leftrightarrow C, \quad H \leftrightarrow (F \wedge E), \quad I \leftrightarrow (H \vee G)
$$

## 5. SAT 求解算法

### 5.1 DPLL 算法

DPLL（Davis-Putnam-Logemann-Loveland,1962）算法 是现代 SAT 求解的核心

基本思想：对公式 $\(\alpha\)$ 执行一系列保持可满足性的转换：
- 若以空子句结束，则UNSAT。
- 若以无子句结束，则SAT。

### 5.2 DP 算法

DP（Davis-Putnam）算法 是 DPLL 的前身，使用消解（Resolution）规则简化公式，但可能导致子句数量的二次增长。

1. 单位传播（Unit Propagation）：
   - 若某子句只有一个文字$\(p\)$：
     - 从所有子句中移除$\(\neg p\)$。
     - 删除包含$\(p\)$的所有子句。
2. 纯文字（Pure Literal）：
   - 若某变量在所有子句中仅以正或负形式出现，则删除包含该文字的所有子句。
3. 消解（Resolution）：
   - 选择一个正负均出现的文字$\(p\)$：
     - $\(P\)$：包含$\(p\)$的子句集合。
     - $\(N\)$：包含$\(\neg p\)$的子句集合。
     - 对每对$\(P\)$和$\(N\)$中的子句进行消解，生成新子句（如$\((p \vee \ell_1) \wedge (\neg p \vee k_1) \rightarrow (\ell_1 \vee k_1)\)$）。
     - 注意：可能导致公式大小平方级增长。

### 5.3 实验结果

以下是不同算法在测试问题上的运行时间（单位：秒）：

| 问题             | tautology | dptaut | dplltaut |
|------------------|-----------|--------|----------|
| prime 3          | 0.00      | 0.00   | 0.00     |
| prime 4          | 0.02      | 0.06   | 0.04     |
| prime 9          | 18.94     | 2.98   | 0.51     |
| prime 10         | 11.40     | 3.03   | 0.96     |
| prime 11         | 28.11     | 2.98   | 0.51     |
| prime 16         | >1 hour   | out of memory | 9.15 |
| prime 17         | >1 hour   | out of memory | 3.87 |
| ramsey 3 3 5     | 0.03      | 0.06   | 0.02     |
| ramsey 3 3 6     | 5.13      | 8.28   | 0.31     |
| mk_adder_test 3 2| >>1 hour  | 6.50   | 7.34     |
| mk_adder_test 4 2| >>1 hour  | 22.95  | 46.86    |
| mk_adder_test 5 2| >>1 hour  | 44.83  | 170.98   |
| mk_adder_test 5 3| >>1 hour  | 38.27  | 250.16   |
| mk_adder_test 6 3| >>1 hour  | out of memory | 1186.4 |
| mk_adder_test 7 3| >>1 hour  | out of memory | 3759.9 |

DPLL算法在大多数问题中表现出更高的效率。

### 5.3 不完备 SAT 算法：GSAT

GSAT 是一种基于局部搜索的算法，通过随机赋值和翻转来寻找满足解：

```plaintext
输入：子句集 F, 最大翻转次数 MAX-FLIPS, 最大尝试次数 MAX-TRIES
输出：满足赋值或空集（若未找到）
for i = 1 to MAX-TRIES
    v = 随机生成的真值赋值
    for j = 1 to MAX-FLIPS
        if v 满足 F then return v
        p = 翻转后增加最多满足子句的变量
        v = 翻转 p 的赋值
    end for
end for
return 空集
```

### 5.4 Stålmarck 方法

Stålmarck 方法 采用广度优先策略，通过 Dilemma Rule 进行 case split，逐步简化公式。

特点：采用广度优先而非深度优先。  
Dilemma Rule：对文字$\(p\)$进行分支：
- 考虑$\(\Delta \cup \{(\neg p)\}\)$和$\(\Delta \cup \{(p)\}\)$。  
- 对每个分支应用基本推导算法$\(R\)$，得到$\(\Delta_0\)$和$\(\Delta_1\)$。  
- 更新$\(\Delta\)$为$\(\Delta_0 \cap \Delta_1\)$。

## 6. 抽象 DPLL

抽象 DPLL 框架 通过状态和转换规则建模 DPLL 算法的执行过程：

- 状态：形如 $\(M \| F\)$，其中 $\(M\)$ 是部分赋值，$\(F\)$ 是 CNF 公式。
- 初始状态：$ \(\emptyset \| F\)$
- 终止状态：
  - $\(fail\)$：表示不可满足。
  - $\(M \| G\)：\(G\)$ 与原公式等满足，且 $\(M\)$ 满足 $\(G\)$.

转换规则

![dpll](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/solver/image/1/dpll.png)

示例：  

![example](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/solver/image/1/example.png)

## 7. SAT 建模

### 7.1 有限状态机建模

对于有限状态机 $\(\mathcal{A} = (Q, Q_0, T)\)$，可以通过以下步骤建模为 SAT 问题：

1. 状态编码：使用 $\(k\)$ 个二进制变量 $\(X = \{x_1, \ldots, x_k\}\)$ 表示状态，满足 $\(|Q| \leq 2^k\)$.
2. 初始状态：编码为 $\(F_{Q_0}(X)\)$.
3. 转移关系：编码为 $\(F_T(X, Y)\)$.
4. 目标状态：编码为 $\(F_U(X)\)$.

### 7.2 BMC

BMC 通过展开转移关系检查在 $\(n\)$ 步内是否能到达目标状态：  
$$ F_{Q_0}(X_0) \wedge F_T(X_0, X_1) \wedge \cdots \wedge F_T(X_{n-1}, X_n) \wedge F_U(X_n) $$

## 8. SMT 求解器

### 8.1 架构

SMT 求解器将问题分解为 SAT 问题和特定理论的决策过程：

- SAT 核心：处理命题逻辑结构。
- 理论求解器：处理特定理论的约束（如算术、数组等）。

### 8.2 支持的理论

SMT 支持多种理论，包括：
- 未解释函数（UF）：处理函数相等性。
- 算术：包括差分逻辑、线性算术、非线性算术。
- 数组：处理读写操作。
- 位向量：处理位级操作。

### 8.3 决策过程示例

以 UF 理论为例，判断公式 $\(x_1 = x_2 \wedge x_2 = x_3 \wedge x_4 = x_5 \wedge x_5 \neq x_1 \wedge F(x_1) \neq F(x_3)\)$ 的可满足性，使用 congruence closure 算法逐步合并等价类，最终得出不可满足。

## 9. SMT 求解方法

### 9.1 急切方法（Eager Approach）

将 SMT 问题直接转换为等价的 SAT 问题。

### 9.2 惰性方法（Lazy Approach）

将 SMT 问题抽象为 SAT 问题，通过与理论求解器交互逐步精炼。

示例：  
对于 $\(\Phi := g(a) = c \wedge f(g(a)) + f(c) \vee g(a) = d \wedge c + d\)$，通过 SAT 和 UF 求解器的多次交互，最终判定不可满足。


## 附录 - 术语

- SAT：Satisfiability，可满足性
- SMT：Satisfiability Modulo Theories，模理论可满足性
- BMC：Bounded model checking，有界模型检查