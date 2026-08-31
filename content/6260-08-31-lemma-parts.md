+++
title = "lemma四部件,requires,ensures,全称变量"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "lemma", "requires", "ensures", "simple"]
toc = true
+++

## lemma-parts.dfy

四个文件里最短的一个,但它是其余三个的地基。

**lemma 不是"函数"。** function 是拿来算东西的:给它输入,它吐出一个值。**lemma 什么都不算——它是一条定理**:一句你向 Dafny 主张"这永远为真"的话,而 Dafny 的工作是替你检查这句话是否真的永远为真。

## 四个部件

```
lemma 名字(参数表)    ← 参数不是"输入"，是数学里的"对任意……"
  requires 前提       ← 定理的"若"（可选；没有就是无条件真理）
  ensures  结论       ← 定理的"则"（这是定理真正主张的内容）
{ 证明体 }            ← 空的 {} 表示"Dafny，你自己看得出来吧"
```

下面这条 lemma,整句读出来是:**"对任意自然数 m、对任意自然数 n:若 m ≤ n,则 2m ≤ 2n。"**

```dafny
lemma simple(m:nat, n:nat)
  requires m <= n
  ensures 2 * m <= 2 * n
{}
```

**空 `{}` 不是"没有证明",而是"证明工作量为零,全部交给自动化"**——这条太简单,Dafny 内置的求解器一眼看穿。

## 思想实验：动它一个部件会怎样

讲义原注释留了三道题:add a return type? add/remove requires/ensures? add/remove parameters? 逐个想清楚会发生什么,对 lemma 的理解就完整了。

1. **加返回类型**(如 `lemma simple(...) : nat`)——**语法错误**。lemma 不计算,没有"返回值"这个概念;要返回值,那是 function 的事。
2. **删掉 requires**——定理变成"对任意 m、n 都有 2m ≤ 2n"。**这是假的**(取 m=5, n=3),Dafny 会拒绝空证明体,报 `a postcondition could not be proved`。教训:**requires 划定定理的适用范围;范围划太大,定理直接为假**。
3. **删掉 ensures**——lemma 依然合法,但**它什么都不主张,是一条空定理**。能通过验证,毫无用处。
4. **删掉参数**(如去掉 n)——ensures 里的 n 变成未定义的名字,**语法错误**。这印证了参数表的真实身份:**它就是 ensures 那句话里"对任意……"所罗列的全称变量清单**。少一个变量,句子就说不通。
5. **加一个没用到的参数**(如 `lemma simple(m:nat, n:nat, k:nat)`)——**完全合法**。定理变成"对任意 m、n、k:……",k 在结论里不出现而已。这也是为什么老师给的 stub 里偶尔有"看似没用"的参数——**它们可能是为后面的证明步骤预留的量词,不要擅自删**。
