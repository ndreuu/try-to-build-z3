module Tree.Tree

type 'T tree = Node of 'T * 'T tree list

module Tree =
  let rec fmap f =
    function
    | Node (v, vs) -> Node (f v, List.map (fmap f) vs)

  let rec fmap2 f x y =
    match (x, y) with
    | Node (v1, vs1), Node (v2, vs2) -> Node (f v1 v2, List.map2 (fmap2 f) vs1 vs2)

  let zip t1 t2 = fmap2 (fun x y -> (x, y)) t1 t2

  let rec fold f x =
    function
    | Node (v, ts) -> f (List.fold (fold f) x ts) v

  let value =
    function
    | Node (v, _) -> v

  let isLastLvl =
    function
    | Node (_, []) -> true
    | _ -> false
