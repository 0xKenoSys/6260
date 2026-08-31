+++
title = "6260 notes: nub,all_distinct,两种分岔,if型case split,member_nub"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "lset", "nub", "all_distinct", "member_nub", "nub_all_distinct"]
toc = true
+++

## all_distinct_nub.dfy：分岔长在布尔条件上

**故事线**:上一个文件的分岔都长在数据形状上(match Nil/Cons)。这个文件的主角 nub 体内藏着一个 `if member(x,xs)`——**分岔长在一个布尔条件上**。于是关于它的证明,也第一次用上 `if { } else { }` 这种**语句形态**的分情况讨论。

**原始文件的一个坑,先交代**:原文件用了 member 却没定义它,include 的 core-list.dfy 里也没有(同目录的 subset-casesplits.dfy 自己定义了 member——若 core-list 里有,那边就会撞名报错)。所以原文件本身过不了:`unresolved identifier: member`。此处补上定义;如果本地的 core-list.dfy 恰好提供了 member,把这段删掉即可。全文件在 Dafny 4.11.0 下验证通过:**5 verified, 0 errors**。

```dafny
include "../core-list.dfy"

predicate member(a : int, A : lset)
{
    match A
    case Nil => false
    case Cons(x,xs) => a == x || member(a,xs)
}
```

## all_distinct 与 nub

all_distinct 读作:空表无重复;Cons(x,xs) 无重复 ⟺ **头 x 不在尾里出现,且尾自己也无重复**。注意 `!` 就是逻辑非——**布尔是一等公民**,`!member(x,xs)` 直接参与 && 运算,不需要 if 包装。

nub 去重,**保留每个元素的最后一次出现**。读作:头 x 若在尾里还会再出现(member(x,xs)),这一份就是冗余,扔掉,只去重尾巴;若不再出现,这是绝版,留下。例:**nub([1,2,1,3]) == [2,1,3]**——第一个 1 被扔(后面还有),第二个 1 留下。

讲义的双关:nub 在英文里是"要旨、核心"——**去重去到只剩本质**。

```dafny
predicate all_distinct(A : lset) {
    match A
    case Nil => true
    case Cons(x,xs) => !member(x,xs) && all_distinct(xs)
}

function nub(A : lset) : lset {
    match A
    case Nil => Nil
    case Cons(x,xs) => if member(x,xs) then nub(xs)
                       else Cons(x,nub(xs))
}   // the "nub" of an issue is its essence
```

## 关于 nub 该证什么：两张体检表

一个改造函数的两张体检表:

1. **它做到了想做的事**:输出确实无重复;
2. **它没做多余的事**:谁是成员这件事一个没动。

只有①没有②的 nub 可以直接返回 Nil 蒙混过关;只有②没有①的 nub 可以原样返回 A。**两条合起来才钉死它。**

## 体检②：member_nub

读作:**对任意 a、A:a ∈ nub(A) ⟺ a ∈ A。** 空 `{}` 即过(实测):自动归纳连同 nub 里的 if 一起消化了。它先过关不只是运气好,**更是下一条定理的原料**。

```dafny
lemma member_nub(a:int, A:lset)
  ensures member(a, nub(A)) <==> member(a, A)
{}
```

## 体检①：nub_all_distinct

空体不行(实测),手写。**证明结构模仿函数结构**:nub 在 Cons 支里 `if member(x,xs)` 分了岔,证明就在同一处、按同一个条件分岔。

**if 支**(x 在尾里还有):nub(Cons(x,xs)) == nub(xs),目标退化成 all_distinct(nub(xs))——归纳假设原句,白送。所以 if 支花括号里**一个字不用写**:分支存在本身就是在向事实云注入"member(x,xs) ⟹ 走这条化简路径"。

**else 支**(x 是绝版):nub(Cons(x,xs)) == Cons(x, nub(xs)),目标展开成两块——ⓐ !member(x, nub(xs)),**缺口**;ⓑ all_distinct(nub(xs)),归纳假设已付。补ⓐ:手里有 ¬member(x,xs)(else 支的入场券),想要的却是关于 nub(xs) 的否定——**差一座"nub 不改成员资格"的桥,正是 member_nub**。实例化 member_nub(x, xs):member(x, nub(xs)) ⟺ member(x, xs) == false。

两支各自封顶,**if 的真假已无所谓,定理成立**。

诚实起见的实测备注:因为 member_nub 是双向等价,把它无条件调用、整个 if/else 骨架拆掉,其实也能过。**保留分岔是因为它如实映照了 nub 的形状——这正是本课要练的那块肌肉。**

```dafny
lemma nub_all_distinct(A : lset)
  ensures all_distinct(nub(A))
{
    match A
    case Nil =>
    case Cons(x,xs) =>
        nub_all_distinct(xs);
        if member(x,xs) {
        } else {
            member_nub(x, xs);
        }
}
```

## 镜像与三笔账

这个证明的形状不是发明出来的,是抄来的——**抄的是 nub 自己的定义**。这一点看清了,剩下全是配账。

目标 all_distinct(nub(Cons(x,xs)))。想展开 nub(Cons(x,xs)),查定义——它的 Cons 分支内部还有一个 `if member(x,xs)`。定义在这里分岔,展开就卡在这里,所以证明必须在同一处分岔。**lemma 里的 if 不是策略,是被 nub 的 if 逼出来的镜像。** 这是上次规则的推论:match 给一层还不够时,**定义里的 if 也算"形状",也要拆**。

`nub_all_distinct(xs)` 放在 if 之前,因为两个分支都要用它——这是归纳假设 ⓑ all_distinct(nub(xs)),**先入账**。

**分支①:member(x,xs) 为真。**

```
定义给出: nub(Cons(x,xs)) == nub(xs)
要:      all_distinct(nub(xs))
有:      归纳假设，一模一样
```

账已平,分支留空。x 是重复品,nub 直接丢掉它,无事发生。

**分支②:¬member(x,xs)。** 注意这条"有"不用写——**走进 else 本身就是入场券,Dafny 自动记账**。

```
定义给出: nub(Cons(x,xs)) == Cons(x, nub(xs))
要（按 all_distinct 的 Cons 分支展开一层）:
   ⓐ ¬member(x, nub(xs))
   ⓑ all_distinct(nub(xs))    ← 归纳假设，已平
```

只剩 ⓐ。手里是 ¬member(x, xs),要的是 ¬member(x, nub(xs))——差一座"nub 不改变成员资格"的桥,正是 member_nub 的双向等价。实例化 member_nub(x, xs),**否定沿等价两边同真同假**,ⓐ 落账。

**整个 body 三行有效代码,每行对应一笔账:归纳假设一笔,桥一笔,空分支一笔。**
