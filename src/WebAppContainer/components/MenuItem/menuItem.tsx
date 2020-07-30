import React from 'react';
import styles from './menuItem.module.css';
import cn from 'classnames';

interface MenuItemProps {
    label: string;
    onClick : () => void;
    iconComp? : any;
    isSelected : boolean
}

export default function MenuItem(props: MenuItemProps) {

    return (
        <div onClick={() => {
            props.onClick();
        }} className={cn(styles.menuItem,props.isSelected && styles.selected)}>
            <div style={{display:'flex', flexDirection :'row'}}>
                {
                    props.iconComp && (
                        <div style={{marginRight:'5px'}}>
                            {props.iconComp}
                        </div>
                    )
                }
                <div>
                    {props.label}
                </div>
            </div>
        </div>
    )

}