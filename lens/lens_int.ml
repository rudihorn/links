module Int = struct
  type t = int [@@deriving eq, show]

  let compare = Stdlib.compare
end

include Int

module Set = struct
  include Lens_set.Make (Int)
end

module Map = struct
  include Lens_map.Make (Int)
end
