import { useState, useEffect } from "react";

function Clock() {
    const [date, setDate] = useState(new Date());

    function refreshClock() {
        setDate(new Date());
    }

useEffect(() => {
    const timeId = setInterval(refreshClock, 1000);
    return function clearup() {
        clearInterval(timeId);
    };
}, []);

return (
    <span>
        {date.toLocaleTimeString()}
    </span>
);
}

export default Clock;
