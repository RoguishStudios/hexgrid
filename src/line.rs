//
// Copyright 2021 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// See LICENSE file for more information

use crate::{Coordinate, Integer};
use num::{One, Zero};
use std::iter;

/// Generic iterator over a line returns x, y values
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineToGen<I: Integer> {
    ax: f32,
    ay: f32,
    bx: f32,
    by: f32,
    n: I,
    i: I,
}

impl<I: Integer> LineToGen<I> {
    pub fn new(ax: f32, ay: f32, bx: f32, by: f32, n: I, i: I) -> LineToGen<I> {
        LineToGen {
            ax,
            ay,
            bx,
            by,
            n,
            i,
        }
    }
}

impl<I: Integer> Iterator for LineToGen<I> {
    type Item = (f32, f32);

    fn next(&mut self) -> Option<Self::Item> {
        if self.n == Zero::zero() {
            if self.i == Zero::zero() {
                self.i += One::one();
                return Some((self.ax, self.ay));
            } else {
                return None;
            }
        }

        if self.i > self.n {
            return None;
        }

        let d = self.i.to_f32().unwrap() / self.n.to_f32().unwrap();
        let x = self.ax + (self.bx - self.ax) * d;
        let y = self.ay + (self.by - self.ay) * d;
        self.i += One::one();
        Some((x, y))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let origin = Coordinate::<I>::nearest(self.ax, self.ay);
        let dest = Coordinate::nearest(self.bx, self.by);
        let total_size = origin.distance(dest) + One::one();
        let len = total_size - self.i;
        let len = len.to_usize().unwrap();
        (len, Some(len))
    }
}

impl<I: Integer> std::iter::FusedIterator for LineToGen<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for LineToGen<I> {}

/// An iterator over an a line of Coordinates
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineToIter<I: Integer>(LineToGen<I>);

impl<I: Integer> LineToIter<I> {
    pub(crate) fn new(gen: LineToGen<I>) -> LineToIter<I> {
        LineToIter(gen)
    }
}

impl<I: Integer> Iterator for LineToIter<I> {
    type Item = Coordinate<I>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(x, y)| Coordinate::nearest(x, y))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: Integer> iter::FusedIterator for LineToIter<I> {}
impl<I: Integer> iter::ExactSizeIterator for LineToIter<I> {}

/// An iterator over an a line of Coordinates, using a lossy algorithm
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineToLossyIter<I: Integer>(LineToGen<I>);

impl<I: Integer> LineToLossyIter<I> {
    pub(crate) fn new(gen: LineToGen<I>) -> LineToLossyIter<I> {
        LineToLossyIter(gen)
    }
}

impl<I: Integer> Iterator for LineToLossyIter<I> {
    type Item = Coordinate<I>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let c = self.0.next().map(|(x, y)| Coordinate::nearest_lossy(x, y));
            match c {
                Some(c @ Some(_)) => return c,
                Some(None) => continue,
                None => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.size_hint().0 / 2, self.0.size_hint().1)
    }
}

impl<I: Integer> iter::FusedIterator for LineToLossyIter<I> {}

/// An iterator over an a line of Coordinates, with edge detection
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineToWithEdgeDetection<I: Integer>(LineToGen<I>);

impl<I: Integer> LineToWithEdgeDetection<I> {
    pub(crate) fn new(gen: LineToGen<I>) -> LineToWithEdgeDetection<I> {
        LineToWithEdgeDetection(gen)
    }
}

impl<I: Integer> Iterator for LineToWithEdgeDetection<I> {
    type Item = (Coordinate<I>, Coordinate<I>);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(x, y)| {
            (
                Coordinate::nearest(x + 0.000001, y + 0.000001),
                Coordinate::nearest(x - 0.000001, y - 0.000001),
            )
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: Integer> iter::FusedIterator for LineToWithEdgeDetection<I> {}
impl<I: Integer> iter::ExactSizeIterator for LineToWithEdgeDetection<I> {}
