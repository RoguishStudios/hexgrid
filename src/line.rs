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

use crate::{Coordinate, Float, Integer, Position};
use std::iter;

/// Generic iterator over a line returns [Position](crate::Position)s.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineGenIter<I: Integer, F: Float> {
    origin: Position<F>,
    target: Position<F>,
    n: I,
    i: I,
}

impl<I: Integer, F: Float> LineGenIter<I, F> {
    pub(crate) fn new(origin: Position<F>, target: Position<F>) -> LineGenIter<I, F> {
        let n = I::from(origin.distance(target)).unwrap();
        let i = I::zero();
        LineGenIter {
            origin,
            target,
            n,
            i,
        }
    }
}

impl<I: Integer, F: Float> Iterator for LineGenIter<I, F> {
    type Item = Position<F>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i > self.n {
            None
        } else if self.n == I::zero() && self.i == I::zero() {
            self.i += I::one();
            Some(self.origin)
        } else {
            let d = F::from(self.i).unwrap() / F::from(self.n).unwrap();
            self.i += I::one();
            Some(Position::from_axial(
                self.origin.q + (self.target.q - self.origin.q) * d,
                self.origin.q + (self.target.r - self.origin.r) * d,
            ))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let origin = Coordinate::from_position(self.origin);
        let target = Coordinate::from_position(self.target);
        let total_size = I::one() + origin.distance(target);
        let len = (total_size - self.i).to_usize().unwrap();
        (len, Some(len))
    }
}

impl<I: Integer, F: Float> std::iter::FusedIterator for LineGenIter<I, F> {}
impl<I: Integer, F: Float> std::iter::ExactSizeIterator for LineGenIter<I, F> {}

/// An iterator over an a line of Coordinates
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineIter<I: Integer, F: Float = f64>(LineGenIter<I, F>);

impl<I: Integer, F: Float> LineIter<I, F> {
    pub(crate) fn new(gen: LineGenIter<I, F>) -> LineIter<I, F> {
        LineIter(gen)
    }
}

impl<I: Integer, F: Float> Iterator for LineIter<I, F> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Coordinate::from_position)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: Integer, F: Float> iter::FusedIterator for LineIter<I, F> {}
impl<I: Integer, F: Float> iter::ExactSizeIterator for LineIter<I, F> {}

/// An iterator over an a line of Coordinates, using a lossy algorithm
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LossyLineIter<I: Integer, F: Float = f64>(LineGenIter<I, F>);

impl<I: Integer, F: Float> LossyLineIter<I, F> {
    pub(crate) fn new(gen: LineGenIter<I, F>) -> LossyLineIter<I, F> {
        LossyLineIter(gen)
    }
}

impl<I: Integer, F: Float> Iterator for LossyLineIter<I, F> {
    type Item = Coordinate<I>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let c = self.0.next().map(Coordinate::from_position_lossy);
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

impl<I: Integer, F: Float> iter::FusedIterator for LossyLineIter<I, F> {}
impl<I: Integer, F: Float> iter::ExactSizeIterator for LossyLineIter<I, F> {}

/// An iterator over an a line of Coordinates, with edge detection
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub struct LineIterWithEdgeDetection<I: Integer, F: Float = f64>(LineGenIter<I, F>);

impl<I: Integer, F: Float> LineIterWithEdgeDetection<I, F> {
    pub(crate) fn new(gen: LineGenIter<I, F>) -> LineIterWithEdgeDetection<I, F> {
        LineIterWithEdgeDetection(gen)
    }
}

impl<I: Integer, F: Float> Iterator for LineIterWithEdgeDetection<I, F> {
    type Item = (Coordinate<I>, Coordinate<I>);

    fn next(&mut self) -> Option<Self::Item> {
        let delta: F = F::from(0.000001).unwrap();
        self.0.next().map(|p| {
            (
                Position::from_axial(p.q + delta, p.r + delta).into_coordinate(),
                Position::from_axial(p.q - delta, p.r - delta).into_coordinate(),
            )
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: Integer, F: Float> iter::FusedIterator for LineIterWithEdgeDetection<I, F> {}
impl<I: Integer, F: Float> iter::ExactSizeIterator for LineIterWithEdgeDetection<I, F> {}
