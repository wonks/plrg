module RecursiveTypes where

data Natural = Inj1 () | Inj2 Natural 

fix :: (t -> t) -> t
fix f = f (fix f)

inj2_infty :: Natural
inj2_infty = fix Inj2