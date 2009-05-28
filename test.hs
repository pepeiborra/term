import Control.Monad.Free
import Data.Term
import Data.Term.Simple
import Data.Term.IOVar

main = do
  let (v0:v1:v2:v3:v4:v5:v6:v7:v8:v9:_) = map var' [0..]
      t1 = f(v0,f(v1, f(v2, f(v3, f(v4, f(v5, f(v6, f(v7, f(v8, f(v9,v9))))))))))
      t2 = f(f(v0,v0), f(f(v1,v1), f(f(v2,v2), f(f(v3,v3), f(f(v4,v4), f(f(v5,v5),
                       f(f(v6,v6), f(f(v7,v7), f(f(v8,v8), f(v9,v9))))))))))
      sol1 = unifies t1 t2

  (v0:v1:v2:v3:v4:v5:v6:v7:v8:v9:_) <- replicateM 10 (liftM Pure freshVar)
  let t1 = f(v0,f(v1, f(v2, f(v3, f(v4, f(v5, f(v6, f(v7, f(v8, f(v9,v9))))))))))
      t2 = f(f(v0,v0), f(f(v1,v1), f(f(v2,v2), f(f(v3,v3), f(f(v4,v4), f(f(v5,v5),
                       f(f(v6,v6), f(f(v7,v7), f(f(v8,v8), f(v9,v9))))))))))
  sol2 <- unifiesIO t1 t2
  print sol1
  print sol2


f (a1,a2) = term "f" [a1,a2]
varsIO = undefined