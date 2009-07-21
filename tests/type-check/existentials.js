relations {
  exists x . x -> Int = exists y . y -> Int
}

expressions {

  function(x) :: Int -> exists x . x {
    return pack Int (exists x . x) in x;
  } :: Int -> exists x . x

}
