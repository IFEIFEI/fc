      ins
   X ---->   F
    \        |
     \       | free
    f \      \/
        ---\  G

        
ins :: (Functor f) => f a -> Free f a
ins fa = Roll (fmap Pure fa)

free :: (Functor f, Monad g) =>
        (forall a. f a -> g a) -> (forall a. Free f a -> g a)
free f (Pure a)  = return a
free f (Roll fa) = join (f (fmap (free f) fa))
