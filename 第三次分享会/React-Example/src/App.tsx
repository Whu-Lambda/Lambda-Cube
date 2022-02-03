import React, { useState } from "react";

export default () => {
    const [a, setA] = useState(1);
    const [b, setB] = useState(2);
  
    function handleChangeA(event: 
      { target: { value: string | number; }; }
      ) 
      {
      setA(+event.target.value);
    }
  
    function handleChangeB(event: 
      { target: { value: string | number; }; }
      ) 
      {
      setB(+event.target.value);
    }
  
    return (
      <div>
        <input type="number" value={a} 
            onChange={handleChangeA} />
        <input type="number" value={b} 
            onChange={handleChangeB} />
  
        <p>
          {a} + {b} = {a + b}
        </p>
      </div>
    );
  };
  
