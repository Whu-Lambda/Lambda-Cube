import ReactDOM from 'react-dom';
import React from 'react';

function Clock(props: { date: 
    { toLocaleTimeString: 
        () => boolean 
            | React.ReactChild 
            | React.ReactFragment 
            | React.ReactPortal; }; }) 
    {
    return (
        <div>
            <h1> Hello,world! </h1>
            <h2>
                It is {props.date.toLocaleTimeString()}.
            </h2>
        </div>
    );
}

function tick() {
    ReactDOM.render(
        <Clock date = {new Date()} />,
        document.getElementById('root')
    );
}

setInterval(tick, 1000);
