open Core.Std
open Sexplib.Conv

open SDN_Types

module type FIELDMAP = sig
  type t 
  module Set : Set.S with type Elt.t = t
  val to_string : ?init:string -> ?sep:string -> t -> string
  val set_to_string : ?init:string -> ?sep:string -> Set.t -> string
  val compare : t -> t -> int    
  val empty : t
  val mk : field -> fieldVal -> t
  val is_empty : t -> bool
  val seq : t -> t -> t option
  val diff : t -> t -> t
  val subseteq : t -> t -> bool
end

module FieldMap : FIELDMAP = struct

  type t = (field * fieldVal) list sexp_opaque with sexp
        
  let to_string ?init:(init="") ?sep:(sep="=") (x:t) : string =
    match x with 
      | [] -> init
      | _ -> 
        List.fold x ~init:""
          ~f:(fun acc (f, v) ->
            Printf.sprintf "%s%s%s%s"
              (if acc = "" then "" else ", " ^ acc)
              (Pretty.string_of_field f)
              sep
              (Pretty.value_to_string v))

  type this_t = t with sexp

  let compare (x:t) (y:t) : int = 
    List.compare x y 
      ~cmp:(fun (f1,v1) (f2,v2) -> 
          let cmp = compare f1 f2 in 
          if cmp <> 0 then cmp 
          else Pervasives.compare v1 v2)

  module Set = Set.Make(struct
    type t = this_t with sexp
    let compare = compare
  end)

  let set_to_string ?init:(init="") ?sep:(sep="=") (s:Set.t) : string =
    Printf.sprintf "{%s}"
      (Set.fold s
         ~init:""
         ~f:(fun acc x -> 
           Printf.sprintf "%s%s"
             (if acc = "" then "" else acc ^ ", ")
             (to_string ~init:init ~sep:sep x)))

  let empty : t = 
    []

  let is_empty (x:t) : bool = 
    match x with 
      | [] -> true
      | _ -> false

  let mk (f:field) (v:fieldVal) : t = 
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
    let map_option f = function
      | None -> None
      | Some x -> Some (f x) in 
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
              (fun o -> k (map_option (fun l -> (fx,vx)::l) o))
          else if cmp < 0 then 
            loop xrest y 
              (fun o -> k (map_option (fun l -> (fx,vx)::l) o))
          else (* cmp > 0 *)
            loop x yrest
              (fun o -> k (map_option (fun l -> (fy,vy)::l) o)) in 
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

module type ACTION = sig
  type t = FieldMap.t
  module Set : Set.S with type Elt.t = t
  type group 
  val to_string : t -> string
  val set_to_string : Set.t -> string
  val group_to_string : group -> string
  val mk : field -> fieldVal -> t
  val seq : t -> t -> t
  val group_mk : Set.t -> group
  val group_union : group -> group -> group
  val group_cross : group -> group -> group
  val id : Set.t 
  val drop : Set.t 
  val is_id : Set.t -> bool
  val is_drop : Set.t -> bool
  val group_id : group
  val group_drop : group
  val group_is_id : group -> bool
  val group_is_drop : group -> bool
end

module Action = struct

  type t = FieldMap.t

  module SetSet = Set.Make(FieldMap.Set)

  module Set = FieldMap.Set

  type group = Set.t list

  let to_string : t -> string = 
    FieldMap.to_string ~init:"" ~sep:":="

  let set_to_string : Set.t -> string = 
    FieldMap.set_to_string ~init:"" ~sep:":="

  let group_to_string (g:group) : string = 
    List.fold g
      ~init:""
      ~f:(fun acc s -> 
           Printf.sprintf "%s%s"
             (if acc = "" then "" else acc ^ "; ")
             (set_to_string s))

  let mk (f:field) (v:VInt.t) : t = 
    FieldMap.mk f v

  let group_mk (s:Set.t) : group = 
    [s]

  let group_union (g1:group) (g2:group) : group = 
    let ss = 
      List.fold g2
        ~init:SetSet.empty
        ~f:(fun acc s -> SetSet.add acc s) in 
    let rec loop g ss k = 
      match g with 
        | [] -> k g2
        | s::grest -> 
          loop grest ss (fun l -> k (s::l)) in 
    loop g1 ss (fun l -> l)

  let group_cross (g1:group) (g2:group) : group = 
    fst (List.fold_right g1
           ~init:([],SetSet.empty)
           ~f:(fun s1i acc -> 
                 List.fold_right g2
                   ~init:acc
                   ~f:(fun s2j acc -> 
                         let g,ss = acc in 
                         let s1is2j = Set.union s1i s2j in 
                         if SetSet.mem ss s1is2j then acc
                         else (s1is2j::g, SetSet.add ss s1is2j))))

  let id : Set.t = 
    Set.singleton (FieldMap.empty)

  let drop : Set.t = 
    Set.empty

  let is_id (s:Set.t) : bool = 
    Set.length s = 1 && 
    match Set.min_elt s with 
      | None -> false
      | Some a -> FieldMap.is_empty a

  let is_drop (s:Set.t) : bool = 
    Set.is_empty s


  let group_id : group = 
    [id]
      
  let group_drop : group = 
    [drop]

  let group_is_id (g:group) : bool = 
    match g with 
      | [s] -> is_id s
      | _ -> false

  let group_is_drop (g:group) : bool = 
    match g with 
      | [s] -> is_drop s
      | _ -> false
end

module type PATTERN = sig
  type t = FieldMap.t
  module Set : Set.S with type Elt.t = t
  type group 
  val to_string : t -> string
  val set_to_string : Set.t -> string
  val group_to_string : group -> string
  val mk : field -> fieldVal -> t
  val seq : t -> t -> t
  val diff : t -> t -> t
  val subseteq : t -> t -> t
end

module Pattern = struct

  type t = FieldMap.t

  module Set = FieldMap.Set

  let to_string : t -> string = 
    FieldMap.to_string ~init:"" ~sep:":="

  let set_to_string : Set.t -> string = 
    FieldMap.set_to_string ~init:"" ~sep:":="

  let mk (f:field) (v:VInt.t) = 
    FieldMap.mk f v

  let seq : t -> t -> t option = 
    FieldMap.seq
      
  let diff : t -> t -> t = 
    FieldMap.diff

  let subseteq : t -> t -> bool = 
    FieldMap.subseteq
end


(* exports *)
type t = unit
let of_policy = failwith "NYI"
let to_netkat = failwith "NYI" 
let compile = failwith "NYI" 
let decompile = failwith "NYI" 
let to_table = failwith "NYI"
