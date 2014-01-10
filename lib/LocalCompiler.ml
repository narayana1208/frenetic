open Core.Std
open Sexplib.Conv

open SDN_Types

module FieldMap : sig 
  type t 
  val compare : t -> t -> int    
  val mk : (field * VInt.t) -> t
  val seq : t -> t -> t option
  val diff : t -> t -> t
end = struct
  type t = (field * VInt.t) list sexp_opaque with sexp

  type this_t = t with sexp

  let compare (x:t) (y:t) : int = 
    List.compare x y 
      ~cmp:(fun (f1,v1) (f2,v2) -> 
          let cmp = compare f1 f2 in 
          if cmp <> 0 then cmp 
          else Pervasives.compare v1 v2)

  let mk ((f,v):field * VInt.t) : t = 
    [(f,v)]

  let rec subseteq (x:t) (y:t) : bool =  
    match x,y with 
      | _,[] -> true
      | [],_::_ -> false
      | (fx,vx)::xrest, (fy,vy)::yrest -> 
        let cmp = Pervasives.compare fx fy in 
        if cmp = 0 then 
          vx = vy && subseteq xrest yrest
        else if cmp < 0 then 
          subseteq xrest y
        else (* cmp > 0 *)
          false

  let rec seq (x:t) (y:t) : t option = 
    let rec loop x y k = 
      match x,y with 
        | _,[] -> 
          k (Some x)
        | [],_::_ -> 
          k (Some y)
        | (fx,vx)::xrest, (fy,vy)::yrest -> 
          let cmp = Pervasives.compare fx fy in 
          if cmp = 0 then 
            loop xrest yrest 
              (fun o -> 
                k ((function 
                    | None -> None 
                    | Some l -> Some ((fx,vx)::l)) o))
          else if cmp < 0 then 
            loop xrest y 
              (fun o -> 
                k ((function 
                    | None -> None
                    | Some l -> Some ((fx,vx)::l)) o))
          else (* cmp > 0 *)
            loop x yrest
              (fun o -> 
                k ((function 
                    | None -> None
                    | Some l -> Some ((fy,vy)::l)) o)) in 
    loop x y (fun o -> o)

  let diff (x:t) (y:t) : t = 
    let rec loop x y k = 
      match x,y with 
        | _,[] -> 
          k x
        | [],_::_ -> 
          k x
        | (fx,vx)::xrest, (fy,vy)::yrest -> 
          let cmp = Pervasives.compare fx fy in 
          if cmp = 0 then 
            loop xrest yrest k 
          else if cmp < 0 then 
            loop xrest y (fun l -> (fx,vx)::l)
          else (* cmp > 0 *)
            loop x yrest k in 
    loop x y (fun o -> o)
end

(* exports *)
type t = unit
let of_policy = failwith "NYI"
let to_netkat = failwith "NYI" 
let compile = failwith "NYI" 
let decompile = failwith "NYI" 
let to_table = failwith "NYI"
