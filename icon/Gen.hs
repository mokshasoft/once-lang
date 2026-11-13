{- Generate once.svg, the Once icon, and once-dark.svg, the same in white
for dark backgrounds. Run `make` in icon/ (in `nix develop`); it runs this
with runghc and renders the PNG and ICO files from once.svg.

The mark: one solid dot (the object 1) and one arrow that leaves it, goes
round a circle, and lands back on it -- the endomorphism main : 1 -> 1, drawn
as the letter O.

The line has one width everywhere and starts at the dot's centre (a ball
terminal); it runs clockwise along the circle and ends in a symmetric head
whose tip and back-edge centre both lie on the circle, so the head aims
slightly inward, at the dot. The whole mark is centred vertically in the
square. All sizes are in units of the 64 x 64 viewBox; angles are SVG angles
(0 = right, growing clockwise), and a distance d along the circle is the
angle d / radius.
-}

import Data.List (intercalate)

size, c :: Double
size = 64
c = size / 2

radius, line, dotR, dotDeg, headLen, headW, tipGap :: Double
radius = 21    -- the circle the line runs along (its centre line)
line = 5.5     -- line width
dotR = 6.5     -- dot radius: visibly heavier than the line
dotDeg = 90    -- where the dot sits (90 = bottom)
headLen = 10   -- arrowhead, tip to back edge
headW = 13     -- arrowhead, width of the back edge
tipGap = 5     -- from the arrow's tip to the dot's edge, along the circle:
               -- keeps the loop visibly open at 16 px

-- the ink of each file: black, and white for dark backgrounds
inks :: [(FilePath, String)]
inks = [("once.svg", "#000000"), ("once-dark.svg", "#ffffff")]

type P = (Double, Double)

-- The point at angle a on the circle of radius r about the origin.
onCircle :: Double -> Double -> P
onCircle r a = (r * cos a, r * sin a)

-- The angles along the line: the dot, the arrow's tip, the head's back
-- edge, and where the line ends (a quarter of the way into the head).
aDot, aTip, aBase, aEnd :: Double
aDot = dotDeg * pi / 180
aTip = aDot + 2 * pi - (dotR + tipGap) / radius
aBase = aTip - headLen / radius
aEnd = aBase + 0.25 * headLen / radius

outer, inner :: Double
outer = radius + line / 2
inner = radius - line / 2

-- The arrowhead: its axis is the chord from the back-edge centre to the tip,
-- both on the circle; the line stays on the circle and enters it slightly
-- askew.
headPts :: [P]
headPts = [tip, (bx + h * nx, by + h * ny), (bx - h * nx, by - h * ny)]
  where
    (bx, by) = onCircle radius aBase
    (ex, ey) = onCircle radius aTip
    m = sqrt ((ex - bx) ^ (2 :: Int) + (ey - by) ^ (2 :: Int))
    (ux, uy) = ((ex - bx) / m, (ey - by) / m)
    tip = (bx + headLen * ux, by + headLen * uy)
    (nx, ny) = (uy, -ux)
    h = headW / 2

dot :: P
dot = onCircle radius aDot

-- Centre vertically: the dot hangs below the ring, so unshifted the mark
-- sits low. The line passes over the top of the circle, so the mark's top
-- is the line's outer edge there.
cy :: Double
cy = c - (top + bottom) / 2
  where
    top = -outer
    bottom = maximum (snd dot + dotR : map snd headPts)

-- From the circle's frame to the square's.
place :: P -> P
place (x, y) = (c + x, cy + y)

-- A number with two decimals, rounding the exact value half to even.
fmt2 :: Double -> String
fmt2 x = sign ++ show q ++ "." ++ pad (show r)
  where
    n = round (toRational x * 100) :: Integer
    sign = if x < 0 || isNegativeZero x then "-" else ""
    (q, r) = abs n `divMod` 100
    pad d = replicate (2 - length d) '0' ++ d

fmt :: P -> String
fmt (x, y) = fmt2 x ++ " " ++ fmt2 y

-- Every subpath is wound clockwise on screen, so the nonzero fill paints
-- their union.

-- The line: the band between the outer and inner circle from aDot to aEnd,
-- clockwise along the outer edge and back along the inner one.
band :: String
band = "M" ++ fmt (at outer aDot)
  ++ " A" ++ fmt (outer, outer) ++ " 0 " ++ large ++ " 1 " ++ fmt (at outer aEnd)
  ++ " L" ++ fmt (at inner aEnd)
  ++ " A" ++ fmt (inner, inner) ++ " 0 " ++ large ++ " 0 " ++ fmt (at inner aDot)
  ++ " Z"
  where
    at r a = place (onCircle r a)
    large = if aEnd - aDot > pi then "1" else "0"

polygon :: [P] -> String
polygon pts = "M" ++ intercalate " L" (map fmt pts') ++ " Z"
  where
    area = sum (zipWith cross pts (drop 1 pts ++ take 1 pts))
    cross (px, py) (qx, qy) = px * qy - qx * py
    pts' = if area < 0 then reverse pts else pts

disc :: P -> Double -> String
disc (x, y) r =
  "M" ++ fmt (x + r, y) ++ " A" ++ rs ++ " 0 1 1 " ++ fmt (x - r, y)
    ++ " A" ++ rs ++ " 0 1 1 " ++ fmt (x + r, y) ++ " Z"
  where rs = show r ++ " " ++ show r

-- The mark as one path: line, head and dot, so no antialiasing seam shows
-- where they meet.
mark :: String
mark = "<path class=\"ink\" d=\""
  ++ unwords [band, polygon (map place headPts), disc (place dot) dotR] ++ "\"/>"

svg :: String -> String
svg ink =
  "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 64 64\" width=\"64\" height=\"64\">\n"
    ++ "  <title>Once</title>\n"
    ++ "  <style>.ink{fill:" ++ ink ++ "}</style>\n  " ++ mark ++ "\n</svg>\n"

main :: IO ()
main = mapM_ (\(file, ink) -> writeFile file (svg ink) >> putStrLn ("wrote " ++ file)) inks
