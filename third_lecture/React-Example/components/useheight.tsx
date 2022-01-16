import { useRef } from "react";
import { useResizeObserver } from "./useResizeObserver";

export const useHeight = <T extends HTMLElement>(
  callback: (height: number) => any
) => {
  let heightRef = useRef<number>(0);

  let observer = useResizeObserver<T>((target) => {
    let height = target.offsetHeight;
    heightRef.current = height;
    callback(height);
  });

  let getCurrentHeight = () => {
    return heightRef.current;
  };

  return {
    ...observer,
    getCurrentHeight
  };
};