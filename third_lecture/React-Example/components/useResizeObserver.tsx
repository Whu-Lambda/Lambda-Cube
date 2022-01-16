import * as React from "react";

const { useLayoutEffect, useRef, useCallback } = React;

const useDispatch = <I extends any[], O>(f: (...args: I) => O): typeof f => {
  let dispatchRef = useRef<typeof f>(f);
  let callback = useCallback<typeof f>((...args) => {
    return dispatchRef.current(...args);
  }, []);

  useLayoutEffect(() => {
    dispatchRef.current = f;
  }, [f]);

  return callback;
};

export const useResizeObserver = <T extends HTMLElement>(
  callback: (target: T) => any
) => {
  let ref = useRef<T | null>(null);
  let observerRef = useRef<ResizeObserver | null>(null);

  let dispatch = useDispatch(callback);

  let trigger = (elem: T | null) => {
    ref.current = elem;

    if (observerRef.current) {
      observerRef.current.disconnect();
      observerRef.current = null;
    }

    if (!elem) return;

    let observer = new ResizeObserver(() => {
      dispatch(elem);
    });

    observer.observe(elem);

    observerRef.current = observer;
  };

  let enable = () => {
    if (ref.current) {
      observerRef.current?.observe(ref.current);
    }
  };

  let disable = () => {
    if (ref.current) {
      observerRef.current?.unobserve(ref.current);
    }
  };

  return {
    trigger,
    enable,
    disable
  };
};
