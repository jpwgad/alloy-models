// book A.3.4. Halmos's shake hands

one sig Alice, Bob extends Person {}
sig Guest extends Person {}
abstract sig Person {
    partner : Person-this,
    shake: set Person-this-partner,
    shakes: #shake
}
fact {
    partner = ~partner
    shake = ~shake
    Alice.partner = Bob     // とは明言されてないけど..
}

fact disjShakes {
    #shakes[Person-Alice] = #(Person-Alice)
}
run {} for 5 int, exactly 10 Person

check {Bob.shakes=4} for 5 int, exactly 10 Person
check {all p:Person | add[p.shakes, p.partner.shakes] = prev[#Person]}
 for 5 int, exactly 20 Person
