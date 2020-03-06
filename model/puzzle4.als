// Die Hard 3 Jugs Problems
open util/ordering [Step]

sig Step {
    action: lone Action,    // 見やすいように何をしたか記録
    small, big: Int         // 各Jugに何ガロン入っているか
}
enum Action { FillSmall, FillBig, EmptySmall, EmptyBig, SmallToBig, BigToSmall }

pred complete[s:Step] { (s.big=4) || (s.big=1 && s.small=3) }
fact {
    // 初期状態
    first.small = 0
    first.big = 0
    no first.action

    // 最終状態
    last.complete

    // Step間遷移
    all s:Step-last | let s'=s.next {
        s.complete => {
            no s'.action
            s'.small = s.small
            s'.big = s.big
        } else {
            fillSmall[s,s'] || fillBig[s,s'] || emptySmall[s,s'] || emptyBig[s,s'] || smallToBig[s,s'] || bigToSmall[s,s']
        }
    }

    // ループ排除：未完了状態では、他Stepと両ジャグの水量が等しくなることはない
    no disj s,s':Step | (!s'.complete) &&
        (s.small=s'.small) && (s.big=s'.big)
}
run {} for 10 Step

let smallCapacity = 3
let bigCapacity = 5
pred fillSmall[s,s':Step] {
    s'.action = FillSmall
    s'.small = smallCapacity
    s'.big = s.big
}
pred fillBig[s,s':Step] {
    s'.action = FillBig
    s'.big = bigCapacity
    s'.small = s.small
}
pred emptySmall[s,s':Step] {
    s'.action = EmptySmall
    s'.small = 0
    s'.big = s.big
}
pred emptyBig[s,s':Step] {
    s'.action = EmptyBig
    s'.big = 0
    s'.small = s.small
}
pred smallToBig[s,s':Step] {
    s'.action = SmallToBig
    let move = min[s.small + bigCapacity.sub[s.big]] {
        s'.big = s.big.add[move]
        s'.small = s.small.sub[move]
    }
}
pred bigToSmall[s,s':Step] {
    s'.action = BigToSmall
    let move = min[s.big + smallCapacity.sub[s.small]] {
        s'.small = s.small.add[move]
        s'.big = s.big.sub[move]
    }
}
