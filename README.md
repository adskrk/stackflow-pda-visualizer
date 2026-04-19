# StackFlow — PDA Visualizer

An interactive web-based simulator for **Pushdown Automata (PDA)** with step-by-step execution, real-time stack visualization, and computation tree analysis.

---

## 🚀 Live Demo

👉 https://adskrk.github.io/stackflow-pda-visualizer/

---

## ✨ Features

* 🎯 **Step-by-step PDA simulation**
* 🗂 **Animated stack memory visualization**
* 🌳 **Computation tree for non-deterministic branching**
* 🔄 **CFG → PDA conversion**
* 🎬 **Playback controls (play, pause, step forward/backward)**
* ⚡ **Multiple example automata (aⁿbⁿ, balanced parentheses, palindromes, etc.)**
* 📊 **Transition table with active rule highlighting**
* 🧠 **Instantaneous Description (ID) tracking**

---

## 🧩 Concepts Covered

This simulator demonstrates key concepts from **Theory of Computation**:

* Pushdown Automata (PDA)
* Non-determinism
* Stack-based computation
* Context-Free Grammars (CFG)
* CFG to PDA conversion
* Acceptance by Final State / Empty Stack

---

## 🛠️ Tech Stack

* HTML5
* CSS3 (custom UI styling)
* Vanilla JavaScript (no frameworks)

---

## 📂 Project Structure

```
.
├── index.html
├── style.css
└── app.js
```

---

## ▶️ How to Use

1. Select an example PDA or load a custom one
2. Enter an input string
3. Click **Run**
4. Observe:

   * Input tape progression
   * Stack operations
   * Active states
   * Computation tree

---

## ⚠️ Assumptions

* Input is validated against the defined alphabet
* Acceptance is checked **after full input consumption**
* Infinite ε-transitions are controlled using a bounded limit

---



## ⭐ Acknowledgment

Inspired by formal language theory concepts and automata simulation tools.
