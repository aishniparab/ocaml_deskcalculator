(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)

(*
have to build a function called compare (for addition and subtraction,
maybe check how long both numbers are and the longer one is bigger. this will require leading zeros to be taken care of though.
*)

open Printf

module Bigint = struct

(*start off by defining some types *)

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list   (*a big int is defined by a sign and then its a list *)
    let  radix    = 10  (*ints are single char in base 10 *)
    let  radixlen =  1  (*each int in this list is of length 1 *)    

    let car       = List.hd 
    let cdr       = List.tl
    let map       = List.map  
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, []) 


(*this function removes leading zeros*)
    let rec rm_zero' list1 = match (list1) with
        | [] -> list1
        | car::cdr1 -> 
                       if car1 != 0
                        then list1
                       else
                        rm_zero' cdr1

(*rm zero calls rm_zero' based on some condition*)
    let rec rm_zero (Bigint (neg1, value1)) = 
        if length value1 > 0
         then (
          let rvrse = reverse value1 in
          Bigint(neg1, reverse (rm_zero' rvrse)))
        else zero

(*check if list value is zero then make it an empty list*)
     let rec is_zero' list1 = match (list1) with
        | [] => true 
        | car1::cdr1 ->
         if car1 = 0
          then is_zero' cdr1
         else false

(*is_zero calls is_zero'*)
    let is_zero (Bigint (neg1, value1)) = 
        if length value > 0
         then (
          if is_zero' value1 = true
          then(zero)
          else Bigint (neg1, value1)
         )
         else zero

(*this is for reading in input *)
    let charlist_of_string str = 
        let last = strlen str - 1  
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

(*converts string to bigint *)
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
(*enables to print out a bigint object *)
    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                   in  strcat ""
                       ((if sign = Pos then "" else "-") ::
                        (map string_of_int reversed))

(*set style of a bigint by removing zeros*)
    let set_style (Bigint(neg1, value1)) = 
        rm_zero(is_zero(Bigint(neg1, value1)))

(*compare to evaluate which list is larger*)
    let rec compare list1 list2 = match (list1, list2) with
        | [], [] -> 0
        | list1, [] -> 1
        | [], list2 -> 2
        | car1:: cdr1, car2:: cdr2 ->
         if car1 > car2
          then 1 
         else if car2 > car1
          then 2
         else compare cdr1 cdr2


    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0  
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->   (*car1::cdr1 is a way to represent a list (appending cdr1 to car1)*)
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)

    let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        (*if the sign is the same use that sign*)
        if neg1 = neg2
         then set_style(Bigint (neg1, add' value1 value2 0))
        (*if one value is pos and one is neg*)
        else if (neg1 = Pos && neg2 = Neg)
         then (
          (*find the larger value and set the sign of sub' result as the sign of larger*)
          if (compare value1 value2) = true
           then set_style(Bigint(neg1, sub' value1 value2 0))
          else set_style(Bigint(neg2, sub' value2 value1 0))
        (*if one value is neg and the other is pos*)
        else (
         if(compare value1 value2) = true
          then set_style(Bigint(neg1, sub' value1 value2 0))
         else set_style(Bigint(neg2, sub' value2 value1 0)))

    let rec sub' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0 -> list1
        | [], list2, 0 -> list2
        | list1, [], carry -> sub' list1 [carry] 0
        | [], list2, carry -> sub' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
            let difference = car1 - car2 - carry
            in difference mod radix :: sub' cdr1 cdr2 (difference/ radix)

     
    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if (neg1 = Pos && neg2 = Pos)
         then (
          if (compare value1 value2) = true
           then set_style(Bigint (Pos, sub' value1 value2 0))
          else set_style(Bigint (Neg, sub' value2 value1 0)))
        else if (neg1 = Neg && neg2 = Pos)
         then (
          if (compare value1 value2) = true
           then set_style(Bigint (Neg, sub' value1 value2 0))
          else set_style(Bigint(Pos, sub' value2 value1 0)))
        else (set_style(Bigint(neg1, add' value1 value2 0)))
   
    let rec mul' list1 list2 pow_of2 double_inp2 prod =
        if (is_zero Bigint(Pos, list1)) = true
         then prod  
        else if (compare list1 pow_of2) = 2
         then (
          let new_list1 = sub (Bigint (Pos, list1)) pow_of2 
          let new_prod = add (Bigint (Pos, prod)) double_inp2
          mul' new_list1 list2 (div_by2 pow_of2 [0]) (div_by2 double_inp2 [0]) new_prod
         ) 
        else (
         mul' list1 list2 (div_by2 pow_of2 [0]) (div_by2 double_inp2 [0]) prod
         )      
     
    let mul (Bigint (neg1, list1)) (Bigint (neg2, list2)) =
        let pow2 = (Bigint (Pos, (pow_of2 list1 1 0)))
        let db_inp2 = (Bigint (Pos, (double_inp2 list2 (pow_of2' list1 1 0))))
        let prod = [] (*problem?*)
        if (get_sign neg1 neg2) = Neg
         then Bigint(Neg, mul' list1 list2 pow2 db_inp2 prod) 
        else Bigint(Pos, mul' list1 list2 pow2 db_inp2 prod)

    let rec div' list1 list2 double_inp2 pow_of2 quot = 
     (*base case where recursion ends?*)
     if (is_zero Bigint(Pos, list2)) = true
      then quot
     else if (is_zero Bigint(Pos, list2)) = true
      then (
       invalid_args "div by zero"
      )   
     else if (compare list2 double_inp2) = 2
      then (
       let new_list2 = sub (Bigint (Pos, list2)) double_inp2
       let new_quot = add (Bigint (Pos, quot)) pow_of2
       div' list1 new_list2 (div_by2 double_inp2 [0]) (div_by2 pow_of2 [0]) new_quot
      )
     else (
      div' list1 list2 (div_by2 double_inp2 [0]) (div_by2 pow_of2 [0]) quot
     ) 
     
    (*check if args are correct*)
     let div (Bigint (neg1, list1)) (Bigint (neg2, list2)) =
      let db_inp2 = (Bigint (Pos, (pow_of2 list1 list2 0)))
      let pow2 = (Bigint(Pos, (double_inp2 [1] (pow_of2' list1 list2 0))))
      let quot = []
      if (get_sign neg1 neg2) = Neg
       then Bigint(Neg, div' list1 list2 db_inp2 pow2 quot)
      else Bigint(Pos, div' list1 list2 db_inp2 pow2 quot)
 
    let rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
      let db_inp2 = (Bigint (Pos, (pow_of2 list1 list2 0)))
      let pow2 = (Bigint(Pos, (double_inp2 [1] (pow_of2' list1 list2 0))))
      let quot = []
      if (get_sign neg1 neg2) = Neg
       then Bigint(Neg, rem' list1 list2 db_inp2 pow2 quot)
      else Bigint(Pos, rem' list1 list2 db_inp2 pow2 quot)
     
    let rec rem' list1 list2 double_inp2 pow_of2 quot =
        let rem = sub (Bigint
     (*PROBLEM WITH DIV AS WELL base case where recursion ends?*)
     if (is_zero Bigint(Pos, list2)) = true
      then list2  (*return remainder instead of quot*)
     else if (is_zero Bigint(Pos, list2)) = true
      then (
       invalid_args "div by zero"
      )
     else if (compare list2 double_inp2) = 2
      then (
       let new_list2 = sub (Bigint (Pos, list2)) double_inp2
       let new_quot = add (Bigint (Pos, quot)) pow_of2
       div' list1 new_list2 (div_by2 double_inp2 [0]) (div_by2 pow_of2 [0]) new_quot
      )
     else (
      div' list1 list2 (div_by2 double_inp2 [0]) (div_by2 pow_of2 [0]) quot
     )
     
     (* value1 is base and value2 is exponent*)
     let pow (Bigint (neg1, base)) (Bigint (neg2, exponent) (Bigint (neg3, result) = 
      if 
      


= match exponent with 
       | 0 -> result
       | exponent when odd exponent -> pow' base (exponent-1) (result * base)
       | exponent       -> pow' (base *. base) (exponent/2) result
       in if n<0 then pow' (1. /. base) (-exponent) 1.
                 else pow' base exponent 1.
       ;;
 

*value1 is base value2 is exponent*)
    let rec pow' value1 value2 accum product
        if (is_zero accum) = true
           then return product
        pow' value1 value2 (sub accum (Bigint (Pos, 1)))
           (mul product  (mul (Bigint(Pos, value1)) (Bigint(Pos, value2))))

    let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        (*if exponent is 0, return 1*)
        if (is_zero (Bigint(neg2, value2))) = true
           then return (Bigint (Pos, 1))
        (*if exponent is negative, return 0*)
        if (neg2 = Neg)
           then return (Bigint (Pos, 0))
        Bigint ret_val = Bigint(Pos, 0)
        (*get return value's number*)
        ret_val = pow' value1 value2 value2 (Bigint (Pos, 1))
       (*get return value's sign*)
        ret_val.sign = Pos
        if (neg1 = Neg)
        then(
           if (even_odd Bigint(neg2, value2)) = false
              then ret_val.sign = Neg
        )
        return ret_val
                                    

     
     
     let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =


 
    (*temp is initially [0]*)
    let rec div_by2 list1 temp
     if (compare list1 temp) = 0
      then list1
     if (compare list1 temp) = 2
      then (sub' temp 1)
     else div_by2 (rm_zero(Pos, (sub' list1 2))) (add' temp 2)
 
    (*needs to be called pow_of2 list1 1 0*)
    let rec pow_of2 list1 pow_val prev_pow = 
     if (compare pow_val list1) = 1
      then (pow_of2 list1 (add pow_val pow_val) pow_val)
     else ( 
      sub pow_val prev_pow
    )    

    (*i should be 0*) 
    let rec pow_of2' list1 pow_val i =
     if (compare pow_val list1) = 1
      then (pow_of2' list1 (add pow_val pow_val) i+1)
     else ( 
      i
    )

    (*i is the result from pow_of2'*)
    let rec double_inp2 list2 i=
     if (i = 0)
      then list2
     else (
      double_inp2 (add list2 list2) (i-1)
     )
  (*result is the sign of product after multiplication*)
  let get_sign (neg1 neg2) = match (neg1 neg2) with
           | Neg, Neg -> return Pos
           | Pos, Pos -> return Pos
           Neg
 
   (*true = even false = odd*)
    let even_odd (Bigint (neg1, value1)) =
      (*even is 2n*)
      if is_zero (rem ((Bigint (neg1, value1)) (Bigint (Pos, 0))))
         then return true
      return false
      (*odd 2n+1*)
end

