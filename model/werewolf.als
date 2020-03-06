// 人狼ゲーム（Are You a Werewolf?）
// https://www.looneylabs.com/lit/rules/are-you-werewolf-rules
open util/ordering [Day]

abstract sig Player {}              // 7-16 players
one sig Moderator in Player {}      // 1 GM (非Playerになるオプションも記載あり)
sig Werewolf extends Player {}      // 2 人狼
sig Seer extends Player {}          // 1 占い師
sig Villager extends Player {}      // other 村人

enum Side {Werewolves, Villagers}
let werewolves[players] = players & Werewolf
let villagers[players] = players & (Seer+Villager)

sig Day {
    alive: set Player,
    seerKnows: set Player,
    lynched: lone alive,
    victim: set (alive-lynched) & (Villager+Seer),
    winner: lone Side,
} {
    let lives = (alive - lynched) {
        (no lives.werewolves) => {
            winner = Villagers
            no victim
        } else (#lives.werewolves >= #lives.villagers) => {
            winner = Werewolves
            victim = lives.villagers
        } else {
            no winner
            #victim = #lives.werewolves
        }
    }
}
fact {
    one Seer
    2 = #Werewolf

    first.alive = Player-Moderator
    first.seerKnows = (Seer & first.alive)
    no first.lynched
    no first.winner
    // one last.winner

    all day:Day-last | let day'=day.next {
        day'.alive = day.alive - day.lynched - day.victim
        (no day'.winner) => {
            one p:day'.alive | p = day'.lynched
        } else {
            no day'.lynched
        }
        (no day'.winner && some Seer & day'.alive) => {
            one p:(day'.alive-day.seerKnows) |
                day'.seerKnows = (day'.alive & day.seerKnows) + p
        } else {
            no day'.seerKnows
        }
    }
}

run {} for 7 Day, exactly 10 Player
