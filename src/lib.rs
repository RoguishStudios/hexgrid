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

//! Hexagonal Grid Map Utility library
//!
//! A lot of ideas taken from [redbloggames hexagon page][hexagon] and [Hex2d-rs][hex2d]
//!
//! [hexagon]: http://www.redblobgames.com/grids/hexagons/
//! [hex2d]: https://github.com/dpc/hex2d-rs

#![doc = "## Flat Topped:"]
#![doc = include_str!("flat.svg")]
#![doc = "## Pointy Topped:"]
#![doc = include_str!("pointy.svg")]
#![forbid(unsafe_code)]
#![warn(clippy::pedantic)]
#![warn(missing_docs)]

mod angle;
mod bearing;
mod coordinate;
mod direction;
mod line;
mod offset;
mod position;
mod range;
mod ring;
mod spacing;
mod spin;
mod spiral;
mod types;

pub use self::angle::Angle;
pub use self::bearing::Bearing;
pub use self::coordinate::Coordinate;
pub use self::direction::Direction;
use self::line::LineToGen;
pub use self::line::{LineToIter, LineToLossyIter, LineToWithEdgeDetection};
pub use self::offset::Offset;
pub use self::position::Position;
pub use self::range::RangeIter;
pub use self::ring::Ring;
pub use self::spacing::{IntegerSpacing, Spacing};
pub use self::spin::Spin;
pub use self::spiral::Spiral;
pub use self::types::{Float, Integer};

#[cfg(test)]
mod tests {
    use crate::Angle::*;
    use crate::Direction::*;
    use crate::*;

    fn with_test_points<F: Fn(Coordinate) -> ()>(f: F) {
        let offs = [-2i32, -1, 0, 1, 2, 1000, -1000, 1001, -1001];
        for &x in offs.iter() {
            for &y in offs.iter() {
                let p = Coordinate::from_cubic(x, y);
                f(p)
            }
        }
    }

    #[test]
    fn coord_add_and_sub() {
        let a = Coordinate::from_cubic(-1, 2);
        let b = Coordinate::from_cubic(3, 4);
        let c = Coordinate::from_cubic(2, 6);

        assert_eq!(a + b, c);
        assert_eq!(c - b, a);
        assert_eq!(c - a, b);
    }

    #[test]
    fn direction_add_and_sub() {
        for &d in Direction::all().iter() {
            assert_eq!(d + Forward, d);
            assert_eq!(d + RightForward + LeftForward, d);
            assert_eq!(d + RightForward + RightForward, d + RightBackward);
            assert_eq!(d + RightForward + RightForward + RightForward, d + Backward);
            assert_eq!(d + LeftForward + LeftForward, d + LeftBackward);
            assert_eq!(d + LeftForward + LeftForward + LeftForward, d + Backward);
            assert_eq!(d + RightBackward + RightBackward + RightBackward, d);
        }

        with_test_points(|c: Coordinate| {
            for &sd in Direction::all() {
                let p = Bearing::new(c, sd);

                assert_eq!(p + Forward, p);
                assert_eq!(p + RightForward + LeftForward, p);
                assert_eq!(p + RightForward + RightForward, p + RightBackward);
                assert_eq!(p + RightForward + RightForward + RightForward, p + Backward);
                assert_eq!(p + LeftForward + LeftForward, p + LeftBackward);
                assert_eq!(p + LeftForward + LeftForward + LeftForward, p + Backward);
                assert_eq!(p + RightBackward + RightBackward + RightBackward, p);
            }
        });
    }

    #[test]
    fn coord_add_and_sub_direction() {
        with_test_points(|c: Coordinate| {
            assert_eq!(c + XY + YX, c);
            assert_eq!(c + ZY + YZ, c);
            assert_eq!(c + ZX + XZ, c);
            assert_eq!(c + ZX + YZ + XY, c);
            assert_eq!(c + XZ + ZY + YX, c);
        });
    }

    #[test]
    fn coord_neighbors() {
        with_test_points(|c: Coordinate| {
            assert_eq!(c, c.neighbors().iter().fold(c, |sc, n| sc + (c - *n)));
        });
    }

    #[test]
    fn move_circularly() {
        with_test_points(|p: Coordinate| {
            let mut start = p;
            let end = p;

            for &dir in Direction::all().iter() {
                start = start + dir;
            }

            assert_eq!(start, end);
        })
    }

    #[test]
    fn move_circularly_double() {
        with_test_points(|p: Coordinate| {
            let mut start = p;
            let end = p;

            for &dir in Direction::all().iter() {
                start = start + dir + dir;
            }

            assert_eq!(start, end);
        });
    }

    #[test]
    fn coord_range() {
        with_test_points(|c: Coordinate| {
            assert_eq!(1, c.range_iter(0).count());
            assert_eq!(7, c.range_iter(1).count());
            assert_eq!(19, c.range_iter(2).count());
            assert_eq!(37, c.range_iter(3).count());
            assert_eq!((5 + 6 + 7 + 8) * 2 + 9, c.range_iter(4).count());
        });
    }

    #[test]
    fn range_distance() {
        with_test_points(|c: Coordinate| {
            for r in 0..10 {
                for p in c.range_iter(r) {
                    assert!(p.distance(c) <= r);
                }
            }
        });
    }

    #[test]
    fn simple_rings() {
        with_test_points(|c: Coordinate| {
            for &d in Direction::all().iter() {
                {
                    // CW r0
                    let ring = c.ring_iter(0, Spin::CW(d)).collect::<Vec<_>>();

                    assert_eq!(1, ring.len());
                    assert_eq!(ring[0], c);
                }
                {
                    // CCW r0
                    let ring = c.ring_iter(0, Spin::CCW(d)).collect::<Vec<_>>();

                    assert_eq!(1, ring.len());
                    assert_eq!(ring[0], c);
                }
                {
                    // CCW r1
                    let ring = c.ring_iter(1, Spin::CW(d)).collect::<Vec<_>>();

                    assert_eq!(6, ring.len());
                    assert_eq!(ring[0], c + d);
                    assert_eq!(ring[1], c + (d + RightForward));
                    assert_eq!(ring[2], c + (d + RightBackward));
                    assert_eq!(ring[3], c + (d + Backward));
                    assert_eq!(ring[4], c + (d + LeftBackward));
                    assert_eq!(ring[5], c + (d + LeftForward));
                }
                {
                    // CCW r1
                    let ring = c.ring_iter(1, Spin::CCW(d)).collect::<Vec<_>>();

                    assert_eq!(6, ring.len());
                    assert_eq!(ring[0], c + d);
                    assert_eq!(ring[1], c + (d + LeftForward));
                    assert_eq!(ring[2], c + (d + LeftBackward));
                    assert_eq!(ring[3], c + (d + Backward));
                    assert_eq!(ring[4], c + (d + RightBackward));
                    assert_eq!(ring[5], c + (d + RightForward));
                }
                {
                    // CW r2
                    let ring = c.ring_iter(2, Spin::CW(d)).collect::<Vec<_>>();

                    assert_eq!(12, ring.len());
                    assert_eq!(ring[0], c + d + d);
                    assert_eq!(ring[1], c + d + d + (d + RightBackward));
                    assert_eq!(ring[7], c - d - d - (d + RightBackward));
                    assert_eq!(ring[11], c + d + d + (d + LeftBackward));
                }
                {
                    // CCW r2
                    let ring = c.ring_iter(2, Spin::CCW(d)).collect::<Vec<_>>();

                    assert_eq!(12, ring.len());
                    assert_eq!(ring[0], c + d + d);
                    assert_eq!(ring[1], c + d + d + (d + LeftBackward));
                    assert_eq!(ring[7], c - d - d - (d + LeftBackward));
                    assert_eq!(ring[11], c + d + d + (d + RightBackward));
                }
                {
                    // CW r-2
                    let ring = c.ring_iter(-2, Spin::CW(d)).collect::<Vec<_>>();

                    assert_eq!(12, ring.len());
                    assert_eq!(ring[0], c - d - d);
                    assert_eq!(ring[1], c - d - d - (d + RightBackward));
                    assert_eq!(ring[7], c + d + d + (d + RightBackward));
                    assert_eq!(ring[11], c - d - d - (d + LeftBackward));
                }
            }
        })
    }

    #[test]
    fn simple_spiral() {
        with_test_points(|c: Coordinate| {
            for &sd in Direction::all() {
                {
                    // CW r0
                    let spiral = c.spiral_iter(0, Spin::CW(sd)).collect::<Vec<_>>();

                    assert_eq!(1, spiral.len());
                    assert_eq!(spiral[0], c);
                }
                {
                    // CCW r0
                    let spiral = c.spiral_iter(0, Spin::CCW(sd)).collect::<Vec<_>>();

                    assert_eq!(1, spiral.len());
                    assert_eq!(spiral[0], c);
                }
                {
                    // CW r1
                    let spiral = c.spiral_iter(1, Spin::CW(sd)).collect::<Vec<_>>();

                    assert_eq!(7, spiral.len());
                    assert_eq!(spiral[0], c);
                    assert_eq!(spiral[1], c + sd);
                    assert_eq!(spiral[2], c + (sd + RightForward));
                    assert_eq!(spiral[3], c + (sd + RightBackward));
                    assert_eq!(spiral[4], c + (sd + Backward));
                    assert_eq!(spiral[5], c + (sd + LeftBackward));
                    assert_eq!(spiral[6], c + (sd + LeftForward));
                }
            }
        });
    }

    #[test]
    fn simple_to_pixel() {
        let p_spacing = Spacing::PointyTop(2f32);
        let f_spacing = Spacing::FlatTop(2f32);

        {
            let c = Coordinate::from_cubic(0, 0);
            assert_eq!(c.to_cartesian_center(p_spacing), (0f32, 0f32));
            assert_eq!(c.to_cartesian_center(f_spacing), (0f32, 0f32));
        }

        assert_eq!(
            Into::<Coordinate<_>>::into((2i32, -1i32)).to_cartesian_center(f_spacing),
            (6f32, 0f32)
        );
        assert_eq!(
            Into::<Coordinate<_>>::into((-2i32, 1i32)).to_cartesian_center(f_spacing),
            (-6f32, 0f32)
        );
        assert_eq!(
            Into::<Coordinate<_>>::into((1i32, 1i32)).to_cartesian_center(p_spacing),
            (0f32, -6f32)
        );
        assert_eq!(
            Into::<Coordinate<_>>::into((2i32, 2i32)).to_cartesian_center(p_spacing),
            (0f32, -12f32)
        );
    }

    #[test]
    fn simple_from_pixel() {
        for &spacing in [
            Spacing::PointyTop(30.0),
            Spacing::PointyTop(-40.0),
            Spacing::FlatTop(100.0),
        ]
        .iter()
        {
            with_test_points(|c: Coordinate| {
                let (x, y) = c.to_cartesian_center(spacing);
                assert_eq!(c, Coordinate::from_pixel(x, y, spacing));
            });
        }
    }

    #[test]
    fn simple_from_pixel_integer() {
        for &spacing in [
            IntegerSpacing::PointyTop(2, 1),
            IntegerSpacing::PointyTop(4, 6),
            IntegerSpacing::FlatTop(3, 2),
        ]
        .iter()
        {
            with_test_points(|c: Coordinate| {
                let ascii_pix = c.to_pixel_integer(spacing);
                let (coord, pix_off) = Coordinate::nearest_with_offset(spacing, ascii_pix);
                assert_eq!((c, (0, 0)), (coord, pix_off));
            });
        }
    }

    #[test]
    fn simple_rotations_around_zero() {
        with_test_points(|c: Coordinate| {
            assert_eq!(
                c,
                c.rotate_around_zero(LeftForward)
                    .rotate_around_zero(RightForward)
            );
            assert_eq!(
                c.rotate_around_zero(LeftBackward),
                c.rotate_around_zero(LeftForward)
                    .rotate_around_zero(LeftForward)
            );
            assert_eq!(
                c.rotate_around_zero(RightBackward),
                c.rotate_around_zero(RightForward)
                    .rotate_around_zero(RightForward)
            );
            assert_eq!(
                c.rotate_around_zero(Backward),
                c.rotate_around_zero(RightForward)
                    .rotate_around_zero(RightForward)
                    .rotate_around_zero(RightForward)
            );
            assert_eq!(
                c.rotate_around_zero(Backward),
                c.rotate_around_zero(LeftForward)
                    .rotate_around_zero(LeftForward)
                    .rotate_around_zero(LeftForward)
            );
            assert_eq!(c.rotate_around_zero(Backward), -c);
        });
    }

    #[test]
    fn simple_rotations_around() {
        with_test_points(|c: Coordinate| {
            with_test_points(|p: Coordinate| {
                assert_eq!(
                    p,
                    p.rotate_around(c, LeftForward)
                        .rotate_around(c, RightForward)
                );
                assert_eq!(
                    p.rotate_around(c, LeftBackward),
                    p.rotate_around(c, LeftForward)
                        .rotate_around(c, LeftForward)
                );
                assert_eq!(
                    p.rotate_around(c, RightBackward),
                    p.rotate_around(c, RightForward)
                        .rotate_around(c, RightForward)
                );
                assert_eq!(
                    p.rotate_around(c, Backward),
                    p.rotate_around(c, RightForward)
                        .rotate_around(c, RightForward)
                        .rotate_around(c, RightForward)
                );
                assert_eq!(
                    p.rotate_around(c, Backward),
                    p.rotate_around(c, LeftForward)
                        .rotate_around(c, LeftForward)
                        .rotate_around(c, LeftForward)
                );
            });
        });
    }

    #[test]
    fn simple_direction_from_center() {
        let c = Coordinate::from_cubic(0, 0);

        assert_eq!(c.direction_from_center_cw(), None);
        assert_eq!(c.direction_from_center_ccw(), None);

        for &dir in Direction::all().iter() {
            assert_eq!((c + dir).direction_from_center_cw(), Some(dir));
            assert_eq!((c + dir).direction_from_center_ccw(), Some(dir));
            assert_eq!(
                (c + dir + (dir + LeftForward)).direction_from_center_cw(),
                Some(dir)
            );
            assert_eq!(
                (c + dir + (dir + RightForward)).direction_from_center_ccw(),
                Some(dir)
            );
        }
    }

    #[test]
    fn simple_direction_to() {
        with_test_points(|c: Coordinate| {
            assert_eq!(c.direction_to_cw(c), None);
            assert_eq!(c.direction_to_ccw(c), None);

            for &dir in Direction::all().iter() {
                assert_eq!(c.direction_to_cw(c + dir), Some(dir));
                assert_eq!(c.direction_to_ccw(c + dir), Some(dir));
                assert_eq!(c.direction_to_cw(c + dir + (dir + LeftForward)), Some(dir));
                assert_eq!(
                    c.direction_to_ccw(c + dir + (dir + RightForward)),
                    Some(dir)
                );
                assert_eq!(
                    c.direction_to_cw(c + dir + (dir + LeftForward) + dir + (dir + LeftForward)),
                    Some(dir)
                );
                assert_eq!(
                    c.direction_to_ccw(c + dir + (dir + RightForward) + dir + (dir + RightForward)),
                    Some(dir)
                );
            }
        });
    }

    #[test]
    fn simple_direction_sub() {
        for &dir in Direction::all().iter() {
            for &angle in Angle::all().iter() {
                assert_eq!((dir + angle) - dir, angle);
            }
        }
    }
    #[test]
    fn simple_line_to() {
        with_test_points(|c: Coordinate| {
            assert_eq!(c.line_to_iter(c).collect::<Vec<_>>(), vec!(c));
        });
    }
}
