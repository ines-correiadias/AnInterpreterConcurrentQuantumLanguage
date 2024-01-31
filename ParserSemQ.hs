-- Functions to obtain semantics results for a program inside a file, given a certain initial state and a linking function.
-- This program is written in our concurrent quantum laguage with non-determinism,
-- with syntax C ::= skip | C ; C | U (q_vec) | Meas (q) -> (C, C) | while Meas (q) -> (skip, C) | C or C | C || C

module ParserSemQ where

import GrammarQ -- module created in GrammarQ.hs
import ParserQ -- module created in ParserQ.hs
import ParserBE_Brookes -- module created in ParserBE_Brookes.hs
import SemQC -- module created in SemQC.hs
import System.Exit -- in order to get type ExitCode (documentation at: https://hackage.haskell.org/package/base-4.18.0.0/docs/System-Exit.html)

-- Applying bigStepList

-- (bigStepListStr str l s) prints on the terminal a String value corresponding to (applyBigStepList c l s), where c is the command corresponding to str
bigStepListStr :: String -> L -> S -> IO ()
bigStepListStr str l s = putStrLn ( showLLConf (applyBigStepList c l s) )
    where c = eitherToT (parseInputC str)

-- (bigStepListFile f l s) prints on the terminal a String value corresponding to applyBigStepList for the command in file f and for linking function l and state s
bigStepListFile :: FilePath -> L -> S -> IO ()
bigStepListFile f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    bigStepListStr program l s

-- Applying smallStepList

-- (nextStepStr str l s) prints on the terminal a String value corresponding to (smallStepList c l s), where c is the command corresponding to str
smallStepListStr :: String -> L -> S -> IO ()
smallStepListStr str l s = putStrLn ( showLLConf (smallStepList c l s) )
    where c = eitherToT (parseInputC str)

-- (nextStepFile f l s) prints on the terminal a String value corresponding to smallStepList for the command in file f and for linking function l and state s
smallStepListFile :: FilePath -> L -> S -> IO ()
smallStepListFile f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    smallStepListStr program l s

-- Applying bigStep

-- (bigStepListStr str l s) prints on the terminal the result of bigStep for the command corresponding to str and for linking function l and state s
bigStepStr :: String -> L -> S -> IO ()
bigStepStr str l s = applyBigStep c l s
    where c = eitherToT (parseInputC str)

-- (bigStepListFile f l s) prints on the terminal the result of bigStep for the command in file f and for linking function l and state s
bigStepFile :: FilePath -> L -> S -> IO ()
bigStepFile f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    bigStepStr program l s

-- Applying smallStep

-- (smallStepSchStr str l s) prints on the terminal the result of smallStep for the command corresponding to str and for linking function l and state s
smallStepStr :: String -> L -> S -> IO ()
smallStepStr str l s = applySmallStep c l s
    where c = eitherToT (parseInputC str)

-- (smallStepSchFile f l s) prints on the terminal the result of smallStep for the command in file f and for linking function l and state s
smallStepFile :: FilePath -> L -> S -> IO ()
smallStepFile f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    smallStepStr program l s

-- Building histograms corresponding to bigStep

-- (histBigStepStr n str l s) plots the same histogram as (histogramBigStep n c l s), where c is the command corresponding to str 
histBigStepStr :: Int -> String -> L -> S -> IO ExitCode
histBigStepStr n str l s = histogramBigStep n c l s
    where c = eitherToT (parseInputC str)

-- (histBigStepFile n f l s) plots the same histogram as (histogramBigStep n c l s), where c is the command in file f
histBigStepFile :: Int -> FilePath -> L -> S -> IO ExitCode
histBigStepFile n f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    histBigStepStr n program l s

-- Building histograms corresponding to smallStep

-- (histSmallStepStr n str l s) plots the same histogram as (histogramSmallStep n c l s), where c is the command corresponding to str
histSmallStepStr :: Int -> String -> L -> S -> IO ExitCode
histSmallStepStr n str l s = histogramSmallStep n c l s
    where c = eitherToT (parseInputC str)

-- (histSmallStepFile n f l s) plots the same histogram as (histogramSmallStep n c l s), where c is the command in file f
histSmallStepFile :: Int -> FilePath -> L -> S -> IO ExitCode
histSmallStepFile n f l s = do
    program <- readFile f -- "program" is a String containing the command in f
    histSmallStepStr n program l s




------------------------------------------------------------------------------------------------------------------------
--useful links: https://hackage.haskell.org/