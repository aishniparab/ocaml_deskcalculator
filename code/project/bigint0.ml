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
        | list1, [] -> true
        | [], list2 -> false
        | car1:: cdr1, car2:: cdr2 ->
         if car1 > car2
          then true
         else if car2 > car1
          then false
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

     
    let sub (input 1, input2)
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
   
   let rec make_divlists' (pow2, multipliers, value)
    if (compare (car multipliers) value) = false
      then(
       (*value > top of multipliers*)
       let pow2 = (add (car pow2) (car pow2)) :: pow2
       let multipliers = 
              (add (car multipliers) (car multipliers)) ::multipliers
       make_lists' pow2 multipliers value
      )

    (*creates lists for div. stops when multipliers list is bigger
      than the other number input*)
    let make_divlists (val1, val2)
       List pow2 = []
       List multipliers = []
       let pow2 = pow2 :: Bigint(Pos, 1)
       let bigger = val1
       let lesser = val2
       if (compare val1 val2) = false
          then( 
           let bigger = val2
           let lesser = val1
          )
       let multipliers = multipliers :: Bigint(Pos, bigger)
       make_lists' (pow2, multipliers, lesser)
       return (pair pow2 multipliers)

    (*creates a pair of lists that act as stacks. 
      one of them is a list of  powers of 2, the 
      other is a list of the input's doubles.
      the lists keep going until the power of 2
      number is bigger that the input value*)
    let make_lists (value)
      (*these better be lists of bigints*)
       List pow2 = []
       List multipliers = []
       let pow2 = pow2 :: Bigint(Pos, 1)
       let multipliers = multipliers :: Bigint(Pos, value)
       make_lists' (pow2, multipliers, value)
       return (pair pow2 multipliers)

    let rec make_lists' (pow2, multipliers, value)
    if (compare (car pow2) value) = false
      then(
       (*value > top of pow*)
       let pow2 = (add (car pow2) (car pow2)) :: pow2
       let multipliers = 
              (add (car multipliers) (car multipliers)) ::multipliers
       make_lists' pow2 multipliers value
      )

    (*does the dirty work for mul, will recurse on
      the lists till the pow2 list is empty.*)
    let rec mul' (pow2, multipliers, sum, sub_value)
        if (is_zero pow2) = true
           then return sum
        if (compare (car pow2) sub_value) = true
           then mul' (cdr pow2) (cdr multipliers) 
                     (add sum (car multipliers)) (sub sub_value (car pow2))
        else mul' cdr pow2 cdr mulitpliers sum sub_value

    let get_sign (neg1 neg2) = match (neg1 neg2) with
           | Neg, Neg -> return Pos
           | Pos, Pos -> return Pos
           return Neg 

    let mul (Bigint (neg1, value1)) (Bigint (neg2, value2))
        (*sum is the rolling sum that we will eventually return. 
         sub_value is whats left to count of the muliplier*)
        Bigint sum = (get_sign neg1 neg2, 0)
        Bigint sub_value = (Pos, value1)
        (*let pow2 multipliers = make_lists value1
        *)
        let p = make_lists value1
        let pow2 = p.fst
        let multipliers = p.snd
        return mul' pow2 multipliers sum sub_value
       
 

    let rec div' (pow2 multipliers sum sub_value)
        if (is_zero pow2) = true
           then return sum
        if (compare (car multipliers) sub_value) = true
           then div' (cdr pow2) (cdr multipliers)
              (add (car pow2) sum) (sub (car multipliers) sub_value)
        else div' (cdr pow2) (cdr multipliers) sum sub_value

    let rec rdiv' (pow2 multipliers sum sub_value)
        if (is_zero pow2) = true
           then return sub_value
        if (compare (car multipliers) sub_value) = true
           then div' (cdr pow2) (cdr multipliers)         
              (add (car pow2) sum) (sub (car multipliers) sub_value)
        else div' (cdr pow2) (cdr multipliers) sum sub_value

(*output of this algo will be quotient and remainder
mod or div will return one or the other of these.
div will always return the int quotient
if its mod you will return the remainder*)
    let div (Bigint (neg1, value1), Bigint (neg2, value2))
        Bigint sum = (get_sign neg1 neg2, 0)
        let bigger = value1
        if (compare value1 value2) = false
           then let bigger = value2
        Bigint sub_value = (Pos, bigger)
        let p = make_divlists(value1, value2)
        let pow2 = p.fst
        let mulitpliers = p.snd
        return div' (pow2, mulitpliers, sum, sub_value)
        
    let rem (Bigint (neg1, value1), Bigint (neg2, value2))
        Bigint sum = (get_sign neg1 neg2, 0)
        let bigger = value1
        if (compare value1 value2) = false
           then let bigger = value2
        Bigint sub_value = (Pos, bigger)
        let p = make_divlists(value1, value2)
        let pow2 = p.fst
        let mulitpliers = p.snd
        return rdiv' (pow2, mulitpliers, sum, sub_value)

(*value1 is base value2 is exponent*)
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

    (*true = even false = odd*)
    let even_odd (Bigint (neg1, value1)) =
      (*even is 2n*)
      if is_zero (rem ((Bigint (neg1, value1)) (Bigint (Pos, 0))))
         then return true
      return false
      (*odd 2n+1*)
end

