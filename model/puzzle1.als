/* レイトン教授 より
    https://www.slideshare.net/osiire/alloy-analyzer
*/

// 本当のことしか言わないトンホー種とウソしか言わないソーウ種
enum 牛種 {トンホー種, ソーウ種}
abstract sig 牛 {type:牛種}
one sig A,B,C,D,E extends 牛 {}     // ５頭の牛がいる

fact {
    #(type.トンホー種) = 2    // ２頭はトンホー種（他はソーウ種）
    // 「X <=> Y」は、(XならばY) かつ (YならばX)
    (A.type = トンホー種) <=> (D.type = ソーウ種)       // A「Dはソーウ種だね」
    (B.type = トンホー種) <=> (C.type != トンホー種)    // B「Cはトンホー種じゃないよ」
    (C.type = トンホー種) <=> (A.type != ソーウ種)      // C「Aはソーウ種じゃない」
    (D.type = トンホー種) <=> (E.type = ソーウ種)       // D「Eはソーウ種です」
    (E.type = トンホー種) <=> (B.type != トンホー種)    // E「Bはトンホー種じゃないぞ」
}

run {}

// 「Bはトンホー種である」に対する反例があるか確認する
check { B.type = トンホー種 }

// 「Dはトンホー種である」に対する反例があるか確認する
check { D.type = トンホー種 }
