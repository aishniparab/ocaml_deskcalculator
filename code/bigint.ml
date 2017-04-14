(*bigint2.ml aishni parab evan hobbs*)

open Printf

module Bigint = struct

(*start off by defining some types *)

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list   
    let  radix    = 10  
    let  radixlen =  1     

    let car       = List.hd 
    let cdr       = List.tl
    let map       = List.map  
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, []) 

let rec compare' list1 list2 = match (list1, list2) with 
        | [], []    -> 0
        | list1, [] -> 1
        | [], list2 -> 2
        | car1:: cdr1, car2:: cdr2 ->
          let x = compare' cdr1 cdr2
          in if x = 0 && car1 !=car2
             then (if car1 > car2
                  then 1
                  else (if car1 < car2
                        then 2
                  else 0))
             else x

let compare (Bigint (neg1, list1)) (Bigint (neg2, list2)) =
        if neg1 = neg2
        then compare' list1 list2
        else if neg1 = Neg
            then 2
            else 1

let rm_zeros list = 
  let rec rm_zeros' list' = match list' with
    | []  -> []
    | [0] -> []
    | car::cdr ->
         let cdr' = rm_zeros' cdr
         in match car, cdr' with 
           | 0, [] -> []
           | car, cdr' -> car::cdr'
         in rm_zeros' list

(*this is for reading in input *)
    let charlist_of_string str = 
        let last = strlen str - 1  
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)
    
    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                   in  strcat ""
                       ((if sign = Pos then "" else "-") ::
                        (map string_of_int reversed))



    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0  
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->          
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)

    let double_bigint number =
        add' number number 0
  
    let rec sub' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0 -> list1
        | [], list2, 0 -> failwith "sub: list2 > list1" 
        | car1::cdr1, [], carry ->
          if car1 = 0  
          then 9 :: (sub' cdr1 [] 1)
          else let diff = car1 - carry*1
               in diff :: (sub' cdr1 [] 0)
        | [], list2, carry -> failwith "sub failed!"
        | car1::cdr1, car2::cdr2, carry ->
          if car2 > (car1 - carry*1)
          then let diff = ((car1 + 10) - carry*1) - car2
               in diff :: (sub' cdr1 cdr2 1)
          else let diff = (car1 - carry*1) - car2
               in diff :: (sub' cdr1 cdr2 0)
    
    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if (neg1 = neg2)
        then (
        if (compare' value2 value1) = 1
        then (Bigint(Neg, rm_zeros(sub' value2 value1 0)))
        else (Bigint(Pos, rm_zeros(sub' value1 value2 0)))
        )  
        else (
        if (compare' value1 value2) = 1
        then (Bigint(neg2, add' value1 value2 0))
        else (Bigint(neg1, add' value2 value1 0))
        )

      let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg1 = neg2
        then (Bigint (neg1, rm_zeros(add' value1 value2 0)))
        else (
        if (compare' value1 value2) = 1
        then (Bigint(neg1, rm_zeros(sub' value1 value2 0)))
        else (Bigint(neg2, rm_zeros(sub' value2 value1 0)))
        )
 
    let rec mul' list1 pow_of2 list2 =
        if (compare' pow_of2 list1) = 1
        then list1, []
        else let remainder, product = 
        mul' list1 (double_bigint pow_of2) (double_bigint list2)
        in if (compare' pow_of2 remainder) = 1
        then remainder, product
        else (rm_zeros(sub' remainder pow_of2 0)), 
             (add' product list2 0)    
 
    let mul (Bigint (neg1, list1)) (Bigint (neg2, list2)) =
        let _, product = mul' list1 [1] list2 in
        if (neg1 = neg2)
        then Bigint(Pos, product)
        else Bigint(Neg, product)

    let rec divrem' dividend pow_of2 divisor =
        if (compare' divisor dividend) = 1
        then [0], dividend
        else 
        let quotient, remainder =
        divrem' dividend 
                (double_bigint pow_of2) 
                (double_bigint divisor)
        in if (compare' divisor remainder) = 1
           then quotient, remainder
           else 
           (add' quotient pow_of2 0), 
           (rm_zeros(sub' remainder divisor 0))

    let divrem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let quotient, remainder = 
        divrem' value1 [1] value2
        in if neg1 = neg2
        then 
        (Bigint (Pos, quotient)), (Bigint (Pos, remainder))
        else 
        (Bigint (Neg, quotient)), 
        (Bigint (Pos, remainder))

    let div (Bigint (neg1, value1)) (Bigint (neg2, value2)) = 
        let quotient, _ = 
        divrem (Bigint (neg1, value1)) 
               (Bigint(neg2, value2))
        in quotient 
 
    let rem (Bigint (neg1, list1)) (Bigint (neg2, list2)) =
        let _, remainder = 
        divrem (Bigint (neg1, list1)) (Bigint (neg2, list2))
        in remainder
    
    (* value1 is base and value2 is exponent*)
    let rec pow' (Bigint (neg1, base)) 
                 (Bigint (neg2, exponent)) 
                 (Bigint (neg3, result)) = 
      match (Bigint (neg2, exponent)) with 
      | (Bigint (neg2, exponent)) when 
        (compare (Bigint (neg2, exponent)) zero) = 0 
        -> (Bigint (neg3, result))
      | (Bigint (neg2, exponent)) 
        -> pow' (Bigint(neg1, base))
                (sub (Bigint (neg2, exponent)) (Bigint (Pos, [1])))
                (mul (Bigint (neg1, base)) (Bigint (neg3, result)))

    let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if (compare (Bigint(neg2, value2)) zero) = 2
        then pow' (div (Bigint (Pos, [1])) (Bigint (neg1, value1)))
                  (Bigint (neg2, value2))
                  (Bigint (Pos, [1])) 
        else pow'
                  (Bigint (neg1, value1))
                  (Bigint (neg2, value2)) 
                  (Bigint (Pos, [1]))              
end
