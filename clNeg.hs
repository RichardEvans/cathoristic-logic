module CLNeg (
     )
where

import Control.Monad
import Data.Either
import Data.List
import Data.Maybe

---------------------------- types ----------------------------

type Symbol = String
data Prop = Top | Bot | Neg Prop | Conj Prop Prop | Disj Prop Prop | Trans Symbol Prop | Bang [Symbol] deriving (Eq, Ord)
type State = Int
type Transition = [(Symbol, [(State, State)])]
data Label = LStar | LBang [Symbol] deriving (Eq, Ord)
type LTS = ([State], Transition, [(State, Label)])
type PointedLTS = (LTS, State)
type Model = Maybe PointedLTS

---------------------------- semantics ----------------------------

satisfies :: Model -> Prop -> Bool
satisfies Nothing _     = True
satisfies (Just m) p    = sats m p

sats :: PointedLTS -> Prop -> Bool
sats _ Top              = True
sats _ Bot              = False
sats m (Neg p)          = not (sats m p)
sats m (Conj p q)       = sats m p && sats m q
sats m (Disj p q)       = sats m p || sats m q
sats m (Trans s p)      = satsArrow m s p
sats m (Bang ss)        = satsBang m ss

satsBang :: PointedLTS -> [Symbol] -> Bool
satsBang ((_,_,ls),w) ss = 
    let (Just l) = lookup w ls
        satsLabel LStar = False
        satsLabel (LBang ss') = ss' `subset` ss
    in  satsLabel l


subset :: (Eq a) => [a] -> [a] -> Bool
subset a b = all (`elem` b) a

satsArrow :: PointedLTS -> Symbol -> Prop -> Bool
satsArrow ((s,r,v), w) a t =
    let satsT (x,y) = w == x && sats ((s,r,v),y) t
        findArrow (a',rel) = a == a' && any satsT rel
    in  any findArrow r

---------------------------- entailment ----------------------------

infix 1 |=
(|=) :: Prop -> Prop -> Bool
(|=) = entails

entails :: Prop -> Prop -> Bool
entails p q = 
    let p2 = removeNeg p q
        ps = dnf p2
        syms = getSymbols p q
        f d = all (`satisfies` q) (expansions (simpl d) syms (degree q))
    in  all f ps
    
getSymbols :: Prop -> Prop -> [Symbol]
getSymbols p q = newSymbol : (nub $ symbols p ++ symbols q)

newSymbol :: Symbol
newSymbol = "_n"

expansions :: Model -> [Symbol] -> Int -> [Model]
expansions Nothing _ _ = [Nothing]
expansions (Just m) ss k = map Just $ f m ss k where
    f m@((_, _, ls), _) ss k =
        let rs = restrictStatesToDepth m k
            ls' = [(w,l) | (w,l) <- ls, w `elem` rs]
        in  nub $ g ls' ss m
    g [] _ m = [m]
    g ((w, l):ls) ss m =
        let ms = expand m (w, l) ss
        in  ms >>= g ls ss

expand :: PointedLTS -> (State, Label) -> [Symbol] -> [PointedLTS]
expand m (w, l) syms =
    let seq = subsequences syms
        checkLabel ss = case l of
            LStar -> True
            LBang ss' -> ss `subset` ss'
        seq' = filter checkLabel seq
    in  map (addTransitions m w) seq'
    
addTransitions :: PointedLTS -> State -> [Symbol] -> PointedLTS
addTransitions m w ss = foldl (addTransition w) m ss

addTransition :: State -> PointedLTS -> Symbol -> PointedLTS
addTransition x m@((states, trans, labels), w) s =
    case satsArrow ((states, trans, labels), x) s Top of
        True -> m
        False -> 
            let newState = (maxState m) + 1
                states' = newState : states
                newTran = (s, [(x, newState)])
                trans' = mergeTransitions trans [newTran]
            in  ((states', trans', labels), w)

restrictStatesToDepth :: PointedLTS -> Int -> [State]
restrictStatesToDepth m@((s, _, _), _) n =
    [w | w <- s, pathLength w m < n]
    
pathLength :: State -> PointedLTS -> Int
pathLength w (lts, root) = f lts [root] w where
    f lts states w | w `elem` states = 0
    f lts states w =
        let outTs = states >>= (\x -> outTransitions (lts, x)) 
            states' = map snd outTs
        in  1 + f lts states' w

---------------------------- simpl ----------------------------

simpl :: Prop -> Model
simpl Top = Just (([1], [], [(1, LStar)]), 1)
simpl Bot = Nothing
simpl (Neg _) = error "Negation should have already been translated away"
simpl (Conj p q) = simpl p `glb` simpl q
simpl (Disj _ _) = error "Disjunction should have already been translated away"
simpl (Trans s p) = do
    m <- simpl p
    return (addSymbolToModel s m)
simpl (Bang ss) = Just (([1], [], [(1, LBang ss)]), 1)

addSymbolToModel :: Symbol -> PointedLTS -> PointedLTS
addSymbolToModel s plts@((states, trans, labels), w) = 
    let newState = (maxState plts) + 1
        states' = newState : states
        labels' = (newState, LStar) : labels
        newTran = (s, [(newState, w)])
        trans' = mergeTransitions trans [newTran]
    in ((states', trans', labels'), newState)

mergeTransitions :: Transition -> Transition -> Transition
mergeTransitions tr1 tr2 = 
    let symbols = (map fst tr1) `union` (map fst tr2)
        f s = case (lookup s tr1, lookup s tr2) of
            (Just r, Nothing) -> (s, r)
            (Nothing, Just r) -> (s, r)
            (Just r, Just r') -> (s, r `union` r')
    in  map f symbols

maxState :: PointedLTS -> Int
maxState ((states, _, _), _) = maximum states

glb :: Model -> Model -> Model
glb Nothing _ = Nothing
glb _ Nothing = Nothing
glb (Just m) (Just m') = f m (uniqueifyStates m' n) where
    n = (maxState m)
    f (lts, w) (lts', w') = do
        lts'' <- merge lts lts' [(w', w)]
        return (lts'', w)

uniqueifyStates :: PointedLTS -> Int -> PointedLTS
uniqueifyStates ((states, trans, labels), w) n = 
    let states' = map (+n) states
        uniqueifyRel rel n = map (\(w, w') -> (w+n, w'+n)) rel
        trans' = map (\(s,rel) -> (s, uniqueifyRel rel n)) trans
        labels' = map (\(s,l) -> (s+n,l)) labels
        w' = w+n
    in ((states', trans', labels'), w')    

merge :: LTS -> LTS -> [(State,State)] -> Maybe LTS
merge m1 m2 ids | ids == [] = Just (addLTSTo m2 m1)
merge m1 m2 ids | ids /= [] =
    if consistentIdentifications m1 m2 ids then
        let m2' = applyIdentifications ids m2
            ids' = getIdentifications m1 m2'
        in  merge m1 m2' ids'
    else 
        Nothing

consistentIdentifications :: LTS -> LTS -> [(State,State)] -> Bool
consistentIdentifications lts lts' ids = all (consistentIdentification lts lts') ids

consistentIdentification :: LTS -> LTS -> (State,State) -> Bool
consistentIdentification lts lts' (w',w) = 
    let pm = (lts, w)
        pm' = (lts', w')
    in  case (getLabel pm, getLabel pm') of
            (LStar, LStar) -> True
            (LStar, LBang ss') -> out pm `subset` ss'
            (LBang ss, LStar) -> out pm' `subset` ss
            (LBang ss, LBang ss') -> out pm `subset` ss' && out pm' `subset` ss
            
getLabel :: PointedLTS -> Label
getLabel ((_, _, labels), w) = fromJust $ lookup w labels

out :: PointedLTS -> [Symbol]
out m = map fst (outTransitions m)

outTransitions :: PointedLTS -> [(Symbol, State)]
outTransitions ((_, t, _), w) =
    let f (s, rel) = (s, fromJust $ lookup w rel)
        succs = filter (fromState w) t
    in  sort $ map f succs

fromState :: State -> (Symbol, [(State, State)]) -> Bool
fromState w (_, rel) = any (\(x,_) -> x == w) rel

applyIdentifications :: [(State,State)] -> LTS -> LTS
applyIdentifications ids lts = foldl replaceState lts ids

replaceState :: LTS -> (State, State) -> LTS
replaceState (states, trans, labels) (x, y) =
    let f s = if s == x then y else s
        f2 (s,s') = case (s==x, s'==x) of
            (True, True) -> (y,y)
            (True, False) -> (y, s')
            (False, True) -> (s, y)
            (False, False) -> (s, s')
        f3 (s,l) = if s == x then (y,l) else (s,l)
        states' = map f states
        trans' = map (\(s,rel) -> (s, map f2 rel)) trans
        labels' = map f3 labels
    in  (states', trans', labels')
    
addLTSTo :: LTS -> LTS -> LTS
addLTSTo (s, t, l) (s', t', l') = 
    let s'' = nub $ s ++ s'
        t'' = t `mergeTransitions` t'
        l'' = mergeLabels l l'
    in  (s'', t'', l'')

mergeLabels :: [(State, Label)] -> [(State, Label)] -> [(State, Label)]
mergeLabels l1 l2 = 
    let states = (map fst l1) `union` (map fst l2)
        moreSpecificL w = case (lookup w l1, lookup w l2) of
            (Nothing, Just l) -> l
            (Just l, Nothing) -> l
            (Just l, Just l') -> moreSpecificLabel l l'
        f s = (s, moreSpecificL s)
    in  map f states

moreSpecificLabel :: Label -> Label -> Label
moreSpecificLabel LStar x = x
moreSpecificLabel x LStar = x
moreSpecificLabel (LBang ss) (LBang ss') = LBang $ ss `intersect` ss'

getIdentifications :: LTS -> LTS -> [(State,State)]
getIdentifications (_, t, _) (_, t', _) =
    let 
        findMatch rel (x,y) = case lookup x rel of
            Just z | y == z -> []
            Just z | y /= z -> [(y, z)]
            Nothing -> []
        findMatches (s, rel) = case lookup s t of
            Nothing -> []
            Just rel' -> map (findMatch rel') rel
    in  concat $ concat $ map findMatches t'

---------------------------- dnf ----------------------------

removeNeg :: Prop -> Prop -> Prop
removeNeg p q = f p (nub $ symbols p ++ symbols q) where
    f :: Prop -> [Symbol] -> Prop
    f Top _ = Top
    f Bot _ = Bot
    f (Neg p) ss =
        let (q, _) = translateNeg (p, (ss, [], []))
        in  q
    f (Conj p q) ss = Conj (f p ss) (f q ss)
    f (Disj p q) ss = Disj (f p ss) (f q ss)
    f (Trans s p) ss = Trans s (f p ss)
    f (Bang ss) _ = Bang ss

dnf :: Prop -> [Prop]
dnf p = extractDisjuncts (fixedPoint dnfStep p)

dnfStep :: Prop -> Prop
dnfStep Top = Top
dnfStep Bot = Bot
dnfStep (Neg _) = error "Negation should have already been translated away"
dnfStep (Conj p (Disj q r)) =
    let p' = dnfStep p
        q' = dnfStep q
        r' = dnfStep r
    in  Disj (Conj p' q') (Conj p' r')
dnfStep (Conj (Disj q r) p) =
    let p' = dnfStep p
        q' = dnfStep q
        r' = dnfStep r
    in  Disj (Conj q' p') (Conj r' p')
dnfStep (Conj p q) = Conj (dnfStep p) (dnfStep q)
dnfStep (Disj p q) = Disj (dnfStep p) (dnfStep q)
dnfStep (Trans s p) = Trans s (dnfStep p)
dnfStep (Bang ss) = Bang ss

extractDisjuncts :: Prop -> [Prop]
extractDisjuncts (Disj p q) = extractDisjuncts p ++ extractDisjuncts q
extractDisjuncts p = [p]

---------------------------- translating negation ----------------------------

translate :: Prop -> [Symbol] -> (Prop, ([Symbol], [Symbol], [Prop]))
translate p ss = fixedPoint translateStep (p, (ss, [], []))

translateStep :: (Prop, ([Symbol], [Symbol], [Prop])) -> (Prop, ([Symbol], [Symbol], [Prop]))
translateStep (Top, cs) = (Top, cs)
translateStep (Bot, cs) = (Bot, cs)
translateStep (Neg p, cs) = translateNeg (p, cs)
translateStep (Conj p q, cs) =
    let (p', cs') = translateStep (p, cs)
        (q', cs'') = translateStep (q, cs')
    in  (Conj p' q', cs'')
translateStep (Disj p q, cs) =
    let (p', cs') = translateStep (p, cs)
        (q', cs'') = translateStep (q, cs')
    in  (Disj p' q', cs'')
translateStep (Trans a p, cs) =
    let (p', cs') = translateStep (p, cs)
    in  (Trans a p', cs')
translateStep (Bang ss, cs) = (Bang ss, cs)

translateNeg :: (Prop, ([Symbol], [Symbol], [Prop])) -> (Prop, ([Symbol], [Symbol], [Prop]))
translateNeg (Top, cs) = (Bot, cs)
translateNeg (Bot, cs) = (Top, cs)
translateNeg (Neg p, cs) = (p, cs)
translateNeg (Conj p q, cs) =
    let (p', cs') = translateNeg (p, cs)
        (q', cs'') = translateNeg (q, cs')
    in  (Disj p' q', cs'')
translateNeg (Disj p q, cs) =
    let (p', cs') = translateNeg (p, cs)
        (q', cs'') = translateNeg (q, cs')
    in  (Conj p' q', cs'')
translateNeg (Trans a p, (ss,path,as)) =
    let ss' = ss \\ [a]
        (p', (_,_,as')) = translateNeg (p, (ss,a:path,as))
        as'' = (makeAssumption path ss) : as'
    in  (Disj (Trans a p') (Bang ss'), (ss,path,as''))
translateNeg (Bang ss, cs@(allSS,_,_)) =
    let f p a = Disj p (Trans a Top)
        ss' = allSS \\ ss
    in  (foldl f Top ss', cs)

fixedPoint :: Eq a => (a->a) -> a -> a
fixedPoint f a = 
    if f a == a then a
    else fixedPoint f (f a)

makeAssumption :: [Symbol] -> [Symbol] -> Prop
makeAssumption [] ss = Bang ss
makeAssumption (h:t) ss = 
    let p = makeAssumption t ss
        d = Disj (Trans h (Bang ss)) (Bang (ss \\ [h]))
    in  Conj p d

symbols :: Prop -> [Symbol]
symbols Top             = []
symbols Bot             = []
symbols (Neg p)         = symbols p
symbols (Conj p q)      = nub $ (symbols p) ++ (symbols q)
symbols (Disj p q)      = nub $ (symbols p) ++ (symbols q)
symbols (Trans a p)     = a : symbols p
symbols (Bang ss)       = ss

degree :: Prop -> Int
degree Top              = 0
degree Bot              = 0
degree (Neg p)          = degree p
degree (Conj p q)       = max (degree p) (degree q)
degree (Disj p q)       = max (degree p) (degree q)
degree (Trans s p)      = 1 + degree p
degree (Bang ss)        = 1

---------------------------- shows ----------------------------

instance Show Prop where
    show t = showProp t 0

showProp (Top) _ = "Top"
showProp (Bot) _ = "Bot"
showProp (Neg p) n | n == 0 = "~" ++ (showProp p (n+1))
showProp (Neg p) n | n >= 1 = "~(" ++ (showProp p (n+1)) ++ ")"
showProp (Conj p q) n | n == 0 = (showProp p (n+1)) ++ " /\\ " ++ (showProp q (n+1))
showProp (Conj p q) n | n >= 1 = "(" ++ (showProp p (n+1)) ++ " /\\ " ++ (showProp q (n+1)) ++ ")"
showProp (Disj p q) n | n == 0 = (showProp p (n+1)) ++ " \\/ " ++ (showProp q (n+1))
showProp (Disj p q) n | n >= 1 = "(" ++ (showProp p (n+1)) ++ " \\/ " ++ (showProp q (n+1)) ++ ")"
showProp (Trans s t) n = "<" ++ s ++ ">" ++ (showProp t (n+1))
showProp (Bang ss) n = "!{" ++ (concat $ intersperse ", " ss) ++ "}"

instance Show Label where
    show LStar = "*"
    show (LBang ss) = "!{" ++ (concat $ intersperse ", " ss) ++ "}"

printModel :: Model -> IO()
printModel Nothing = putStrLn "Nothing"
printModel (Just m) = printPointedLTS m

printPointedLTS :: PointedLTS -> IO()
printPointedLTS ((s, t, l), w) = do
    putStrLn "Worlds: "
    putStr "    "
    mapM_ putStr (intersperse ", " (map show s))
    putStrLn ""
    putStrLn "Transitions:"
    mapM_ (\x -> putStrLn ("    " ++ (show x))) t
    putStrLn "Labels:"
    mapM_ (\x -> putStrLn ("    " ++ (show x))) l
    putStrLn ("Current world:" ++ show w)
    putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"


---------------------------- testing ----------------------------

t1 = not $ (Disj (Trans "a" Top) (Trans "b" Top)) |= (Trans "b" Top)

t2 = (Bang ["a"]) |= (Bang ["a", "b"])

t3 = not $ (Bang ["a", "b"]) |= (Disj (Bang ["a"]) (Trans "b" Top))

t4 = (Conj (Bang ["a"]) (Trans "b" Top)) |= (Trans "c" Top)

t5 = not $ (Conj (Bang ["a"]) (Trans "a" Top)) |= (Trans "c" Top)

t6 = (Bang ["a", "b"]) |= (Bang ["b", "a"])

t7 = Conj (Disj (Trans "a" Top) (Trans "b" (Trans "a" Top))) (Disj (Trans "b" (Bang [])) (Trans "c" Top)) |= Disj (Trans "a" Top) (Trans "c" Top)

t8 = Trans "a" (Trans "b" Top) |= Trans "a" Top

t9 = not $ Trans "a" Top |= Bang ["a"]

t10 = not $ Trans "a" Top |= Neg (Trans "b" Top)

t11 = not $ Disj (Bang ["b"])(Trans "a" (Bang ["a", "b"])) |= Disj (Trans "a" (Trans "b" Top)) (Disj (Bang ["b"]) (Trans "a" (Bang ["a"])))

t12 = Conj (Bang ["a", "c"]) (Bang ["b", "c"]) |= Bang ["c"]

t13 = Conj (Disj (Trans "a" $ Trans "c" Top) (Trans "b" $ Trans "d" Top)) (Neg $ Trans "a" Top) |= Trans "b" Top

t14 = not $ Trans "a" (Bang ["a", "b"]) |= Disj (Trans "a" (Trans "b" Top)) (Trans "a" (Bang ["a"]))

t15 = not $ Conj (Bang ["a"]) (Trans "a" Top) |= Trans "a" (Bang [])

t16 = not $ Conj (Bang ["a"]) (Trans "a" (Trans "b" Top)) |= Trans "a" (Conj (Trans "b" Top) (Bang ["b"]))

t17 = not $ Trans "a" (Conj (Trans "b" Top) (Bang ["b"])) |= Trans "a" (Conj (Trans "c" Top) (Bang ["c"]))

t18 = not $ Trans "a" Top |= Trans "b" Top

t19 = not $ Trans "a" Top |= Conj (Trans "a" Top) (Bang ["a"])

t20 = not $ Trans "a" (Trans "b" Top) |= Trans "b" (Trans "a" Top)

t21 = not $ Conj (Trans "a" (Bang [])) (Trans "b" (Bang [])) |= Trans "a" (Trans "b" Top)

t22 = Conj (Trans "a" Top) (Conj (Trans "b" Top) (Trans "c" Top)) |= Trans "b" Top

t23 = Trans "a" Top |= Top

t24 = Trans "a" (Trans "b" Top) |= Trans "a" Top

t25 = not $ Trans "a" (Trans "b" Top) |= Trans "b" Top

t26 = Bot |= Trans "a" Top

t27 = Conj (Bang []) (Trans "a" Top) |= Trans "b" Top

t28 = Trans "a" Bot |= Trans "b" Top

t29 = Conj (Trans "a" (Trans "b" Top)) (Trans "a" (Trans "c" Top)) |= Trans "a" (Conj (Trans "b" Top) (Trans "c" Top))

t30 = Conj (Bang ["b"]) (Trans "a" Top) |= Trans "c" Top

t31 = Trans "a" (Conj  (Trans "b" Top) (Conj  (Trans "c" Top)  (Trans "d" Top))) |= Trans "a" (Trans "c" Top)

t32 = Conj (Trans "a" (Conj (Bang ["b"]) (Trans "b" Top))) (Trans "a" (Bang [])) |= Trans "c" Top

t33 = Conj (Trans "c" (Conj (Trans "b" Top) (Trans "c" (Bang [])))) (Trans "c" (Trans "c" (Trans "a" Top))) |= Trans "d" Top

tests = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33]

test = all id tests

proveExcludedMiddle :: Prop -> Bool
proveExcludedMiddle p = 
    let ss = symbols p
        (p', (_, _, as)) = translate (Neg p) ss
        lhs = foldl Conj Top as
        rhs = Disj p p'
    in  lhs |= rhs
    
p1 = proveExcludedMiddle (Trans "a" Top)
p2 = proveExcludedMiddle (Trans "a" (Trans "b" Top))
p3 = proveExcludedMiddle (Trans "a" (Conj (Trans "a" Top) (Trans "b" Top)))
p4 = proveExcludedMiddle (Conj (Trans "a" Top) (Trans "b" Top))


m1 = simpl $ Conj (Trans "a" (Bang ["c"])) (Trans "b" (Trans "d" Top))
m2 = simpl $ Conj (Trans "a" (Trans "c" Top)) (Trans "b" (Bang ["d"]))
m3 = m1 `glb` m2