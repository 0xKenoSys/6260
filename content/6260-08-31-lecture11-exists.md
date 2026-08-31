+++
title = "6260 notes: exists,witness,取证人:|,∀∃与∃∀,mem_nth"
date = 2026-08-31
categories = ["6260"]
tags = ["Dafny", "exists", "witness", "ghost", "divides_transitive", "boundExists", "mem_nth"]
toc = true
+++

## univ-recap.dfy：全称量词只有两个动作

**为什么先复盘 forall?** 因为这一课的主角 exists 的全部招式,都是 forall 招式的**镜像**。先把 forall 的两个动作钉牢,exists 的两个动作就是照镜子。

**动作一,证明一个 forall = 任意元法**:"设 x 为任意一个满足守卫的值……(对这个 x 完成证明)……由 x 之任意性,命题对一切 x 成立。"Dafny 语法就是第十课的 forall 语句:`forall x | 守卫 ensures 目标(x) { 对这个 x 的证明 }`。

**动作二,使用一个 forall = 实例化法**:手里有"对一切 x 成立",想用时挑一个具体值代进去。**调 lemma 传参数就是实例化**(参数表 = for all 清单,调用 = 逐个填值);对 requires 里的 forall,Dafny 多数时候自动挑值实例化。

**原始文件的真相,先交代**:下面两条 lemma 原样**都证不出来**(实测:2 errors)。q 是无体谓词,第一条无任何前提却要凭空证出关于 q 的全称——**无米之炊**;第二条前提全是 q 的事实,结论却问 r——**文不对题**。这文件是讲师的白板骨架:上课时现场改造它来演示上面两个动作。所以"答案"不是硬证原文,而是两个改造后的可证变体,一个动作一个。(本文件整体在 Dafny 4.11.0 下验证通过:**3 verified, 0 errors**。)

**变体一,演示动作一**。给它一个像样的前提(q 对一切成立),求证带守卫的窄版全称。体内的 forall 语句就是"设 x 为任意一个正数"这句数学话的机器写法:花括号里 x 是可触碰的名字;此处目标 q(x) 由前提实例化直接得到,所以括号里一个字不用写。(诚实备注,实测:这条其实**空体也能过**——前提太强,求解器自动实例化就够了。保留 forall 语句是为了见过它的全形,真正非它不可的战例在第十课 reverse_subset 里已经打过。)

```dafny
predicate q(x:int)   // 无体谓词：任意未知性质
predicate r(x:int)

lemma somename_arbitrary()
  requires forall x :: q(x)
  ensures forall x | 0 < x :: q(x)
{
    forall x | 0 < x ensures q(x) {
    }
}
```

**变体二,演示动作二及其陷阱**。前提说:对一切**正数** x,q(x) 成立。结论想要 q(y/103)。**实例化不是白拿的:挑的值必须满足守卫 0 < x。** y 是 nat,y/103 完全可能等于 0(y < 103 时)——0 不是正数,守卫不满足,实例化非法,原样必挂。补一条 requires y >= 103,则 y/103 ≥ 1,守卫达标,空体即过。**带走的教训:用 forall 时,Dafny 替你把守卫当关卡查;挑的值过不了守卫,"对一切"就轮不到它。**

```dafny
lemma somename_instantiate(y:nat)
  requires forall x | 0 < x :: q(x)
  requires y >= 103    // 补上的门票：保证 y/103 > 0
  ensures q(y / 103)
{}
```

**预告:镜像表。** 记住这张表,本课其余四个文件就是右列的实战:

```
            证明它                    使用它
forall      任意元（forall 语句）      实例化（代具体值）
exists      出示证人（assert 实例）    取证人（var w :| P）
```

forall 的证明难在"任意",使用容易;exists 恰好反过来:**证明只需亮出一个例子,使用时却要把藏着的家伙抓出来。**

## exists-witness.dfy：动作一,出示证人

**exists 是什么**:`exists i :: P(i)` 读作"存在一个 i 使 P(i) 成立"。要证明它,数学上只需一件事:亮出一个具体的例子——术语叫**证人(witness)**。"存在大于 2 小于 4 的整数吗?""存在,3 就是。"举证完毕,无需多言。

**语法铁律的另一半**:第十课说过 forall 配 ==>;它的镜像是 **exists 配 &&**。若写出 exists 配 ==>,几乎必然错了——"存在一个 x,若它…则…"在 x 取不满足前件的值时空真,**说了等于没说**。

全文件 Dafny 4.11.0 实测:**2 verified, 0 errors**。

fitsBetween(x, lo, hi):x 严格落在 (lo, hi) 区间内。两个语法点:①**链式比较 `lo < x < hi` 是合法 Dafny**,等价 lo < x && x < hi(lab01 练过的 inRange 同款);②requires lo < hi 给谓词设了门槛:区间得像个区间。于是任何提到 fitsBetween(…,a,b) 的地方,Dafny 都会顺手检查 a < b——**规格自己也有规格**。

```dafny
predicate fitsBetween(x : int, lo : int, hi : int)
  requires lo < hi
{
    lo < x < hi
}
```

定理读作:存在整数 i 落在 2 和 4 之间。(参数 j 通篇未用——老师的 stub 就长这样,原样保留。)

**原样无体,如何补证?出示证人。** 整数里夹在 2 和 4 之间的只有 3,把它亮出来。求解器验完这条具体断言(3 确实 > 2 且 < 4,顺带查过 2 < 4 的门槛),事实云里就有了 fitsBetween 的一个**具体实例**——而 exists 的触发器正是 fitsBetween(i,2,4) 这个应用样式,**具体实例一进云,模式立刻对上,存在命题应声成立**。

**对照组,别忘了**:第十课的 smallestExists 同是"喂证人",为何那边喂不进?因为那边的公式体 s <= m 没有函数应用、没有把手;这边 fitsBetween(…) 就是现成的把手。**证人法能否奏效,成败全在触发器。**

```dafny
lemma exist1(j:int)
  ensures exists i : int :: fitsBetween(i,2,4)
{
    assert fitsBetween(3,2,4);   // 补全：出示证人 3
}

/* This is a very "maths-y" example; next one will be
   more Computer Science... */
```

## divides-trans.dfy：动作二,取证人（:|）

上一个文件练了"证明 exists = 出示证人";本文件练镜像动作:**使用 exists = 把藏着的证人抓出来**。语法是 `var w :| P;`——第十课 subset_forall 里惊鸿一瞥的那个记号,今天正式拜师。全文件 Dafny 4.11.0 实测:**1 verified, 0 errors**。

**新定义方式**:上一课的 divides 用取模 n % m == 0,这里换成教科书原味:**m 整除 n ⟺ 存在倍数 q 使 q·m == n**。exists 直接住进了谓词定义里。

**ghost 是什么**:"幽灵"标记 = **此物只活在证明世界,永不编译成可运行代码**。为何必须:真跑这个谓词,机器得在无穷多个 q 里搜一个满足 q·m == n 的——**无界搜索没法执行**。取模版是程序(可算),exists 版是数学(可证不可算);**ghost 就是在类型系统里给这道界线立的碑**。规格尽可以奢侈地用数学,只要别指望运行它。

```dafny
ghost predicate divides(m:nat, n:nat)
{
    // "ghost" means we (don't want to/can't) run this as code
    exists q:nat :: q * m == n
}
```

定理读作:m 整除 n,n 整除 p,则 m 整除 p(整除的传递性)。**先想数学证明,再翻译**:m|n 意味着有个 a 使 a·m == n;n|p 意味着有个 b 使 b·n == p;于是 p == b·n == b·(a·m) == (b·a)·m——**(b·a) 就是 m|p 所需的证人**。三步:抓两个证人,拼出第三个。

逐行翻译:

- `var a :| a * m == n;`——**"取证人"语句**。读作:前提保证有这么个 a 存在,抓一个出来,命名为 a,此后 a·m == n 是可用事实。**合法性由 Dafny 当场审查**:它必须能证明确有此物(此处 requires divides(m,n) 展开即是)。抓出来的 a 只知满足条件,别的一概不知——**存在只欠你一个,不欠更多**。
- `var b :| b * n == p;`——同法抓第二个证人。
- `assert (b * a) * m == b * (a * m);`——**乘法结合律**。非线性算术是求解器软肋(solve_poly 旧事),这条恒等式喂给它当踏脚石;有了它,(b·a)·m == b·(a·m) == b·n == p 一路等下来。
- `assert (b * a) * m == p;`——**出示证人收尾**:这条具体实例进了事实云,ensures 里 exists q :: q * m == p 的模式立刻匹配上(证人正是 b·a)。

**抓两个,拼一个,亮出来——两个动作在同一个证明里首尾相接。**

```dafny
lemma divides_transitive(m:nat, n:nat, p:nat)
  requires divides(m,n)
  requires divides(n,p)
  ensures divides(m,p)
{
    var a :| a * m == n;
    var b :| b * n == p;
    assert (b * a) * m == b * (a * m);
    assert (b * a) * m == p;
}
```

## intlist-bound.dfy：证人接力,与量词顺序

讲义预告的 "more Computer Science" 来了:**数据结构上的存在证明**。新难度:证人不再像 3 那样一眼看穿,得在归纳过程中**逐层建造**——每层从下层手里接过旧证人,加工出本层的新证人。全文件 Dafny 4.11.0 实测:**3 verified, 0 errors**。

exceeds(i, l):i 严格大于 l 中的每个元素(i 是 l 的**严格上界**)。空表:真(无人可越,空真);Cons:越过头,且越过尾中所有。

```dafny
include "../core-list.dfy"

predicate exceeds(i:int, l:list<int>) {
    match l
    case Nil => true
    case Cons(h,t) => i > h && exceeds(i,t)
}
```

"will probably need an intermediate lemma"——讲义原话,预言成真。这就是那条中间引理:**上界单调性**,若 m 已是 l 的上界,任何 k ≥ m 也是。为什么需要它?往下看主定理的 Cons 支就明白:**从尾巴抓来的旧证人 m 可能不够高(比不过新头 h),得垫高;垫高之后"对尾巴仍是上界"这件事不是白送的**——正是本引理的职责。空体即过:自动归纳沿 l 一路放行。

```dafny
lemma exceedsBigger(m: int, k: int, l: list<int>)
  requires exceeds(m, l)
  requires m <= k
  ensures exceeds(k, l)
{}
```

主定理读作:**任何整数列表都存在严格上界**。(有限列表当然有上界;无限就没有——**有限性是隐形英雄**。)

**证人接力,逐支拆账**。Nil 支:随便谁都是空表的上界,出示证人 0。Cons(h,t) 支,四步接力:

1. boundExists(t)——**归纳假设**:尾巴那边存在上界;
2. `var m :| exceeds(m, t)`——**取证人**:把尾巴的上界抓出来叫 m;
3. **建造本层证人 k**:得同时压过 h 和整条尾巴——取 m 与 h+1 的较大者(h+1 保证**严格**大于 h;写 max 的 if-then-else 即可,注意这是函数体位置,**用表达式 if,不是证明里的语句 if**);
4. exceedsBigger(m, k, t)——**垫高背书**:k ≥ m,故 k 仍是尾巴的上界;连同 k > h,assert exceeds(k, l) 成立——出示证人,收工。

**抓证人 → 加工证人 → 亮新证人:归纳存在证明的标准舞步。**

```dafny
lemma boundExists(l : list<int>)
  ensures exists m :: exceeds(m,l)
{
    match l
    case Nil =>
        assert exceeds(0, Nil);
    case Cons(h,t) =>
        boundExists(t);
        var m :| exceeds(m, t);
        var k := if m > h + 1 then m else h + 1;
        exceedsBigger(m, k, t);
        assert exceeds(k, l);
}
```

"flip quantifiers, prove something else"——讲义结尾的思考题:把量词翻个面会怎样?我们证的是(把 lemma 的隐式 forall 写出来):

```
∀ l · ∃ m · exceeds(m, l)    每条列表各有各的上界  ✓
∃ m · ∀ l · exceeds(m, l)    有一个万能上界压住一切列表  ✗
```

后者是假的:任你报出 m,造 Cons(m, Nil) 一击致命——m > m 不成立。**同样的字,换个顺序,真变假。**

**铭刻:∀∃ 与 ∃∀ 是两个世界**——前者允许证人随 l 变(接力棒一层层换人),后者要求一个证人包打天下。**读写嵌套量词时,顺序是第一要务。**

## list-nth.dfy：压轴,member 的 exists 刻画

**收官的对称**:第十课压轴是 subset 的 forall 刻画(循环 ⟺ 全称);本课压轴是 member 的 exists 刻画(查找 ⟺ 存在):**"i 在列表里" ⟺ "存在一个下标 n,第 n 位恰好是 i"**。一负一正,两把量词各配一台递归机器,**课程闭环**。全文件 Dafny 4.11.0 实测:**4 verified, 0 errors**。

member:查成员,老朋友(此处用 `function ... : bool` 写法,与 predicate 完全同义——**predicate 就是它的糖衣**)。nth(l, n):取第 n 个元素(0 起数)。**match 没写 Nil 支**——requires n < length(l) 保证 l 非空(Nil 长度为 0,没有任何 n < 0 的 nat),Nil 支不可达,Dafny 认可省略。**前置条件砍掉死分支**,lab03 就见过这一手。

```dafny
function member(i : int, l : list<int>) : bool
{
    match l
    case Nil => false
    case Cons(h,t) => h == i || member(i,t)
}

function nth<T>(l : list<T>, n : nat) : T
  requires n < length(l)
{
    match l
    case Cons(h,t) => if n == 0 then h else nth(t, n - 1)
}
```

定理读作:i ∈ l ⟺ 存在下标 n(n < length(l))使 nth(l,n) == i。注意 **exists 也能用竖线守卫**:`exists n | 守卫 :: 公式`,等价于 `exists n :: 守卫 && 公式`——看,**exists 配的是 &&**。

**为什么是全课最重的一条?** iff 两个方向各要一门手艺:**⟹ 方向,从"在里面"要建造出下标——证人构造题;⟸ 方向(逆否),从"不在里面"要证没有任何下标可行——否定存在 = 全称否定,得请出 forall 语句逐个排除。** 一条定理同时用上两把量词的证明动作,故为压轴。

**逐段拆账**。对 l 归纳,Nil 支双空(没成员也没下标),留白。Cons(h,t) 支先调 mem_nth(i,t) 领归纳假设(尾巴版的 iff),再按 member(i,l) 真假分岔:

**◆ member 为真——建造证人**,再分两小岔:i 就是头,证人是下标 0,亮出来;i 在尾里,由归纳假设的 ⟹ 向,尾巴那边存在下标——取出证人 n,尾巴的第 n 位在整条列表里是第 n+1 位(头占了 0 号),**证人平移后亮出**。

**实战细节,实测踩过**:`:|` 的变量要**显式标注 : nat**——ensures 里的 exists 量化在 nat 上,抓出来的证人不标类型会被推断成 int,后续 n+1、nth 的下标约束全线飘红(4 个 error),**标上即愈**。

**◆ member 为假——排除一切证人**:目标是 ¬exists,即 forall n | n < length(l) :: nth(l,n) != i。证 forall 用任意元法(univ-recap 动作一):forall 语句拎出任意下标 n 逐个审问——n == 0 时 nth(l,0) 是头 h,h != i(否则 member 早真了);n > 0 时喂一条换算 nth(l,n) == nth(t,n-1),**把问题踢回尾巴**;归纳假设的 ⟸ 向说尾巴无此成员则尾巴无此下标,排除完毕。

```dafny
lemma mem_nth(i : int, l : list<int>)
  ensures member(i, l) <==> exists n : nat | n < length(l) :: nth(l,n) == i
{
    match l
    case Nil =>
    case Cons(h,t) =>
        mem_nth(i, t);
        if member(i, l) {
            if h == i {
                assert nth(l, 0) == i;                            // 证人：0
            } else {
                var n : nat :| n < length(t) && nth(t, n) == i;   // 取尾巴的证人
                assert nth(l, n + 1) == i;                        // 平移后亮出
            }
        } else {
            forall n : nat | n < length(l) ensures nth(l, n) != i {
                if n > 0 {
                    assert nth(l, n) == nth(t, n - 1);            // 踢回尾巴
                }
            }
        }
}
```
