---
weight: 1
title: "What is Formal Verification"
description: "What is Formal Verification"
---

## 1. A Brief Description

Formal verification is a static verification technique that uses mathematical logic and algorithms to comprehensively analyze system designs, aiming to prove or refute their compliance with specific properties or specifications.

## 2. The Concept of Formal Verification

For very-large-scale integration (VLSI) designs, there are currently two main methods for functional verification: dynamic simulation verification and formal verification. Formal verification uses mathematical methods to compare the logical functions of the original design and the modified design. In contrast, dynamic simulation applies identical stimuli to both designs and observes their responses.

Formal Verification is a static verification technique and an essential tool for addressing the challenges of verifying complex chips. Unlike simulation verification, formal verification does not rely on test cases but instead performs a comprehensive analysis of the design using mathematical logic and algorithms.

## 3. Fundamental Techniques of Formal Verification

### 1. Model Checking

Model checking is an automated method used to verify the properties of finite-state systems. It formalizes and verifies SystemVerilog Assertions (SVA) properties and uses algorithms to traverse all possible states, checking whether the design satisfies the given properties.

Typically, model checking and formal property verification (FPV) are considered synonymous. Common FPV tools include Synopsys's VC Formal FPV App and Cadence's Jasper FPV App.

Model checking is a foundational technology that has spawned related tools, such as coverage analysis tools like Synopsys's VC Formal FCA App and Cadence's Jasper UNR App, and connectivity checking tools like Synopsys's VC Formal CC App and Cadence's Jasper CONN App.

**Advantages:**
- Automated
- No need to provide proof
- Capable of diagnosing counterexamples

**Disadvantages:**
- Writing SVA can be challenging
- State space explosion issues

### 2. Equivalence Checking

Equivalence checking compares two designs to ensure they have identical functionality, often used to verify the correctness of design modifications. It ensures that optimizations or changes do not introduce new errors by comparing the behavior of two designs.

Equivalence checking is highly effective and can be applied at various stages of design, such as from C to RTL (typically pre-synthesis verification), RTL to netlist (pre-synthesis verification), or netlist to netlist (pre- and post-place-and-route verification or ECO verification).

Furthermore, equivalence checking can be divided into Logic Equivalence Checking (LEC) and Sequential Equivalence Checking (SEC).

- **LEC**: Ensures two designs are logically identical, producing the same outputs for the same inputs. LEC focuses on functional correctness without considering timing behavior. Due to its simplicity and efficiency, LEC is widely used, with tools like Synopsys's Formality and Cadence's Conformal being common choices.

- **SEC**: Verifies that two designs are equivalent not only in logic but also in timing behavior, ensuring their delays and timing constraints are identical. While SEC provides comprehensive guarantees of both functional correctness and timing consistency, it is computationally intensive and resource-heavy, making it less commonly applied in complex designs. Siemens' OneSpin excels in this area.

### 3. Theorem Proving

Theorem proving relies on mathematical logic and reasoning to construct logical chains that verify the correctness of system designs.

Theorem proving is a powerful formal verification method, offering a higher level of rigor and correctness guarantee than model checking but requiring greater complexity and resource consumption.

It is especially suitable for fields and projects with stringent demands for reliability, safety, and functional correctness, such as multiplier verification.

ACL2 is a well-known theorem prover, and both Intel and AMD have used it to verify their floating-point multipliers.

## 4. Related Terminology

- **FV**: Formal Verification
- **SVA**: SystemVerilog Assertions
- **FPV**: Formal Property Verification
- **UNR/FCA**: UNR (Unreachability Coverage); FCA (Formal Coverage Analyzer)
- **CC/CONN**: Connectivity Checking
- **LEC**: Logic Equivalence Checking
- **SEC**: Sequential Equivalence Checking
