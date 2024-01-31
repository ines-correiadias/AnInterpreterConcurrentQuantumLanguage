module HistogramSem where

import Graphics.Histogram -- (documentation at: https://hackage.haskell.org/package/Histogram-0.1.0.2/docs/Graphics-Histogram.html)
import qualified Graphics.Gnuplot.Frame.OptionSet as Opt -- (documentation at: https://hackage.haskell.org/package/gnuplot-0.5.7/docs/Graphics-Gnuplot-Frame-OptionSet.html)
import System.Exit -- in order to get type ExitCode (documentation at: https://hackage.haskell.org/package/base-4.18.0.0/docs/System-Exit.html)

-- Building a histogram with integer data, with one column for each integer, with caption "<conf x>" for integer (x-1)

dataSet1 = [1,0,0,1,1,1,1,2,3,4,5,6,7,8,9,10,20] -- integer data for testing


-- (histogramInt dataSet t) plots an histogram whose input is dataSet and whose title is t, with the following features:
---- the bin size is 1, so there is one column for each integer; 
---- the range of the x-axis is from -1 to (max+1), where max is the largest element of dataSet;
---- in the x-axis, integer (x-1) has caption "<conf x>", and only integers from 0 to (max-1) are labeled.

-- The elements of dataSet are all expected to be integers.

histogramInt :: [Double] -> String -> IO ExitCode
histogramInt [] title = error "Empty input."
histogramInt dataSet title = plotAdv "" options hist -- the filename (1st argument of plotAdv) is empty, so the histogram will appear on a new window
    where max = round (maximum dataSet) :: Int -- (maximum dataSet) is of type Double, but max is of type Int; max is the largest element of dataSet
          hist = histogramBinSize 1 dataSet -- (histogramBinSize 1 dataSet) creates a histogram with bin size 1 and with dataSet as its input
          options = Opt.title title $ Opt.xRange2d (-1,max+1) $ Opt.xTicks2d (xTicksData max) (defOpts hist) -- options for the histogram (title, range of the x-axis and labels of the x-axis)

-- options is of type PlotOptions, with PlotOptions = Graphics.Gnuplot.Frame.OptionSet.T (Graphics.Gnuplot.Graph.TwoDimensional.T Int Double)
-- Opt.title :: C graph => String -> T graph -> T graph
-- Opt.xTicks2d :: (C x, C y, C x) => [(String, x)] -> T (T x y) -> T (T x y)

xTicksData :: Int -> [(String,Int)] -- xTicksData m = [("<conf 1>",0), ("<conf 2>",1), ... ("<conf m>", m-1)]
xTicksData m = xTicksDataAux 0 m

xTicksDataAux :: Int -> Int -> [(String,Int)] -- auxiliary to xTicksData
xTicksDataAux n m
    | (n == m) = []
    | otherwise = ("<conf "++(show (n+1))++">", n) : xTicksDataAux (n+1) m

--------------------------------------

-- useful links:

-- http://learnyouahaskell.com/
-- https://hackage.haskell.org/
-- specifically:
-- https://hackage.haskell.org/package/Histogram-0.1.0.2/docs/Graphics-Histogram.html (contains a useful example)
-- https://hackage.haskell.org/package/gnuplot-0.5.7/src/src/Demo.hs (also contains some useful examples)

-- https://wiki.haskell.org/Converting_numbers (mentions useful functions for converting numbers)