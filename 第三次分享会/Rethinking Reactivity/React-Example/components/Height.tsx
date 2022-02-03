import * as React from "react";
import "./styles.css";
import { useHeight } from "./useheight";

const { useState, useEffect } = React;

export default function App() {
  let [height, setHeight] = useState(0);
  let [status, setStatus] = useState(true);

  let handleStatusChange = (event: React.ChangeEvent<HTMLInputElement>) => {
    setStatus(event.target.checked);
  };

  let observer = useHeight<HTMLTextAreaElement>((currentHeight) => {
    if (currentHeight > 300) {
      if (height !== 300) {
        setHeight(300);
      }
    } else {
      setHeight(currentHeight);
    }
  });

  useEffect(() => {
    if (!status) {
      observer.disable();
    } else {
      observer.enable();
    }
  }, [status, observer]);

  return (
    <div style={{ minHeight: 100 }}>
      <textarea ref={observer.trigger} />
      <div>height is {height}</div>
      <form>
        <div>
          <label>Observer enabled:</label>
          <input
            type="checkbox"
            checked={status}
            onChange={handleStatusChange}
          />
        </div>
      </form>
    </div>
  );
}
