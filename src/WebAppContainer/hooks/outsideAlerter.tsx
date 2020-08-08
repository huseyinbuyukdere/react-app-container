import React, { useRef, useEffect } from "react";
/**
 * Hook that alerts clicks outside of the passed ref
 */
function useOutsideAlerter(ref:any, onClickOutside : any) {   
  useEffect(() => {
    /**
     * Alert if clicked on outside of element
     */
    function handleClickOutside(event:any) {
      if (ref.current && !ref.current.contains(event.target)) {
        if(onClickOutside){
            onClickOutside();
        }
      }
    }
    // Bind the event listener
    document.addEventListener("mousedown", handleClickOutside);
    return () => {
      // Unbind the event listener on clean up
      document.removeEventListener("mousedown", handleClickOutside);
    };   
  // eslint-disable-next-line react-hooks/exhaustive-deps  
  }, [ref]);
}

/**
 * Component that alerts if you click outside of it
 */
function OutsideAlerter(props :OutsideAlerterProps) {
  const wrapperRef = useRef(null);
  useOutsideAlerter(wrapperRef,props.onClickOutside);

  return <div ref={wrapperRef}>{props.children}</div>;
}


interface OutsideAlerterProps {
    onClickOutside : () => void;
    children : any
}

export default OutsideAlerter;