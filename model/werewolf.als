// 人狼ゲーム（Are You a Werewolf?）
// https://www.looneylabs.com/lit/rules/are-you-werewolf-rules
open util/ordering [Day]

abstract sig Player {}              // 7-16 players
one sig Moderator in Player {}      // 1 GM (非Playerになるオプションも記載あり)
sig Werewolf extends Player {}      // 2 人狼
sig Seer extends Player {}          // 1 占い師
sig Villager extends Player {}      // other 村人

enum Side {Werewolves, Villagers}
let werewolves[players] = (players & Werewolf)
let villagers[players] = players & (Seer+Villager)

sig Day {
    alive: set Player,                              // 朝の時点で生き残っている人々
    seerKnows: set Player,                          // 占い師が正体を知っている生き残り
    lynched: lone alive,                            // 昼間選ばれた被処刑者
    victim: set (alive-lynched) & (Villager+Seer),  // 夜の犠牲者
    winner: lone Side,                              // 勝利陣営
} {
    // 朝の判定
    (no alive.werewolves) => {
        // 人狼がいなければ村人側の勝利
        winner = Villagers
        no lynched
        no victim
    } else (#alive.werewolves) >= (#alive.villagers) => {
        // 人狼が村人以上いれば人狼側の勝利
        winner = Werewolves
        no lynched
        victim = alive.villagers
    } else {
        // 初日以外ならひとり処刑される
        this!=first => one lynched

        // 夕方の判定
        let alive' = (alive - lynched) {     // 夕方の生き残り
            (no alive'.werewolves) => {
                // 人狼がいなければ村人側の勝利
                winner = Villagers
                no victim
            } else (#alive'.werewolves) >= (#alive'.villagers) => {
                // 人狼が村人以上いれば人狼側の勝利
                winner = Werewolves
                victim = alive'.villagers
            } else {
                // 未決着なら人狼の数だけ犠牲者が出る
                no winner
                #victim = #alive'.werewolves
            }
        }
    }
}
fact {
    one Seer
    2 = #Werewolf

    first.alive = Player-Moderator          // 役柄不明なGMを外す
    first.seerKnows = (Seer & first.alive)  // (GMでなければ)占い師自身のことは知っている
    no first.lynched
    no first.winner
    // one last.winner

    all day:Day-last | let day'=day.next {
        day'.alive = day.alive - day.lynched - day.victim
        (no day'.winner) && (some Seer & day'.alive) => {
            // (未決着で)占い師がいるなら、生き残りのうちひとりの正体を知る
            one p:(day'.alive-day.seerKnows) |
                day'.seerKnows = (day'.alive & day.seerKnows) + p
        } else {
            no day'.seerKnows
        }
    }
}

run {} for 7 Day, exactly 10 Player
