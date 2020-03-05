// シマウマのパズル
// https://qiita.com/Soichir0/items/daa0b9df8a2500ae0a04

// 家が5軒一列に並んで建っている
// 5軒の家はそれぞれ違う色に塗られていて、住んでいる人はそれぞれ生まれた国、
// 飼っているペット、飲み物、履物の種類が違う
enum Color {Blue, Green, Red, Yellow, Cream}
enum Nationality {Denmark, Japanese, Bolivian, Scottish, Greece}
enum Pet {Snails, Dog, Horse, Fox, Zebra}
enum Drink {Tea, Orange, Milk, Coffee, Water}
enum Footwear {Leather, Slipper, LeatherS, BeachS, Platform}

abstract sig House {
    color: disj Color,
    left,right: lone House
}
one sig House1,House2,House3,House4,House5 extends House {}
fact 家は一列に並ぶ {
    right = House1->House2 + House2->House3 + House3->House4 + House4->House5
    left = ~right       // 左は右の反対
}

sig Person {
    house: disj House,
    nationality: disj Nationality,
    pet: disj Pet,
    drink: disj Drink,
    footwear: disj Footwear
}

fact {
    nationality.Scottish.house.color = Red  // スコットランド人は赤い家に住んでいる
    nationality.Greece.pet = Dog            // ギリシャ人は犬を飼っている
    drink.Coffee.house.color = Green        // コーヒーを飲むのは緑色の家の人
    nationality.Bolivian.drink = Tea        // ボリビア人はお茶を飲む
    color.Green = color.Cream.right         // 緑色の家はクリーム色の家のすぐ右隣りにある
    footwear.Leather.pet = Snails           // 革靴を履いている人はカタツムリを飼っている
    footwear.Platform.house.color = Yellow  // 厚底靴を履くのは黄色の家の人
    drink.Milk.house = House3               // 牛乳を飲むのは真ん中の家の人
    nationality.Denmark.house.left = none   // デンマーク人は左端の家に住んでいる
    // 革サンダルを履いている人は、キツネを飼っている人の隣の家に住んでいる
    footwear.LeatherS.house in pet.Fox.house.(left+right)
    // 厚底靴を履いている人はの家は、ウマを飼っている家の隣
    footwear.Platform.house in pet.Horse.house.(left+right)
    footwear.Slipper.drink = Orange         // スリッパを履いている人はオレンジジュースを飲む
    nationality.Japanese.footwear = BeachS  // 日本人はビーチサンダルを履いている
    // デンマーク人は青い家の隣に住んでいる
    nationality.Denmark.house in color.Blue.(left+right)
}
// 問題：水を飲むのは誰？ シマウマを飼っているのは誰？

run {} for exactly 5 House, exactly 5 Person